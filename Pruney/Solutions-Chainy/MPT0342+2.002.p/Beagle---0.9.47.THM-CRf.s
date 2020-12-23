%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 530 expanded)
%              Number of leaves         :   20 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 (1430 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_2192,plain,(
    ! [A_292,B_293] :
      ( r2_hidden('#skF_2'(A_292,B_293),A_292)
      | r1_tarski(A_292,B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2212,plain,(
    ! [A_294] : r1_tarski(A_294,A_294) ),
    inference(resolution,[status(thm)],[c_2192,c_8])).

tff(c_113,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_43,B_44] :
      ( ~ v1_xboole_0(A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_131,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1('#skF_2'(A_41,B_42),A_41)
      | v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_113,c_24])).

tff(c_55,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_7')
      | ~ r2_hidden(D_27,'#skF_6')
      | ~ m1_subset_1(D_27,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_59,plain,(
    ! [D_27] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_27,'#skF_6')
      | ~ m1_subset_1(D_27,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_155,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_34,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,'#skF_7')
      | ~ r2_hidden(D_21,'#skF_6')
      | ~ m1_subset_1(D_21,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    ! [D_21] :
      ( m1_subset_1(D_21,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_21,'#skF_6')
      | ~ m1_subset_1(D_21,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_204,plain,(
    ! [D_57] :
      ( m1_subset_1(D_57,'#skF_7')
      | ~ r2_hidden(D_57,'#skF_6')
      | ~ m1_subset_1(D_57,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_106])).

tff(c_220,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_204])).

tff(c_228,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_220])).

tff(c_229,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_233,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_229])).

tff(c_234,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,(
    ! [B_25,A_26] :
      ( v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_54,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_324,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | v1_xboole_0(k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_345,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_324])).

tff(c_355,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_345])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_517,plain,(
    ! [B_97,B_98,A_99] :
      ( r2_hidden(B_97,B_98)
      | ~ r1_tarski(A_99,B_98)
      | ~ m1_subset_1(B_97,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_529,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,'#skF_5')
      | ~ m1_subset_1(B_97,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_355,c_517])).

tff(c_555,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_5')
      | ~ m1_subset_1(B_100,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_529])).

tff(c_568,plain,(
    ! [B_100] :
      ( m1_subset_1(B_100,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_100,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_555,c_24])).

tff(c_610,plain,(
    ! [B_103] :
      ( m1_subset_1(B_103,'#skF_5')
      | ~ m1_subset_1(B_103,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_568])).

tff(c_628,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_610,c_229])).

tff(c_632,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_107,c_628])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_632])).

tff(c_641,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_731,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121))
      | v1_xboole_0(k1_zfmisc_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_749,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_731])).

tff(c_759,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_749])).

tff(c_172,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52),B_53)
      | ~ r1_tarski(A_52,B_53)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_188,plain,(
    ! [B_53,A_52] :
      ( ~ v1_xboole_0(B_53)
      | ~ r1_tarski(A_52,B_53)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_172,c_2])).

tff(c_765,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_759,c_188])).

tff(c_768,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_765])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_768])).

tff(c_772,plain,(
    m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_796,plain,
    ( v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_772,c_30])).

tff(c_797,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_910,plain,(
    ! [B_137,A_138] :
      ( r1_tarski(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_138))
      | v1_xboole_0(k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_931,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_910])).

tff(c_941,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_931])).

tff(c_1197,plain,(
    ! [B_169,B_170,A_171] :
      ( r2_hidden(B_169,B_170)
      | ~ r1_tarski(A_171,B_170)
      | ~ m1_subset_1(B_169,A_171)
      | v1_xboole_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_1209,plain,(
    ! [B_169] :
      ( r2_hidden(B_169,'#skF_5')
      | ~ m1_subset_1(B_169,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_941,c_1197])).

tff(c_1238,plain,(
    ! [B_172] :
      ( r2_hidden(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1209])).

tff(c_1254,plain,(
    ! [B_172] :
      ( m1_subset_1(B_172,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_172,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1238,c_24])).

tff(c_1294,plain,(
    ! [B_174] :
      ( m1_subset_1(B_174,'#skF_5')
      | ~ m1_subset_1(B_174,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_797,c_1254])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_2'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_892,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_136,'#skF_7'),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_136,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_896,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_892])).

tff(c_902,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_896])).

tff(c_1308,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1294,c_902])).

tff(c_1312,plain,
    ( v1_xboole_0('#skF_6')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_124,c_1308])).

tff(c_1319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_131,c_1312])).

tff(c_1321,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_1472,plain,(
    ! [B_198,A_199] :
      ( r1_tarski(B_198,A_199)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_199))
      | v1_xboole_0(k1_zfmisc_1(A_199)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_1494,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_1472])).

tff(c_1505,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1494])).

tff(c_1373,plain,(
    ! [D_188,B_189] :
      ( r2_hidden(D_188,B_189)
      | ~ r1_tarski('#skF_7',B_189)
      | ~ r2_hidden(D_188,'#skF_6')
      | ~ m1_subset_1(D_188,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_156])).

tff(c_1385,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_1'('#skF_6'),B_189)
      | ~ r1_tarski('#skF_7',B_189)
      | ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1373])).

tff(c_1393,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_1'('#skF_6'),B_189)
      | ~ r1_tarski('#skF_7',B_189)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1385])).

tff(c_1395,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_1'('#skF_6'),B_190)
      | ~ r1_tarski('#skF_7',B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1393])).

tff(c_1424,plain,(
    ! [B_190] :
      ( ~ v1_xboole_0(B_190)
      | ~ r1_tarski('#skF_7',B_190) ) ),
    inference(resolution,[status(thm)],[c_1395,c_2])).

tff(c_1511,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1505,c_1424])).

tff(c_1518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1511])).

tff(c_1522,plain,(
    ! [D_200] :
      ( ~ r2_hidden(D_200,'#skF_6')
      | ~ m1_subset_1(D_200,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_1534,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_1522])).

tff(c_1541,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1534])).

tff(c_1545,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1541])).

tff(c_1546,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1545])).

tff(c_1696,plain,(
    ! [B_226,A_227] :
      ( r1_tarski(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(A_227))
      | v1_xboole_0(k1_zfmisc_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_1717,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_1696])).

tff(c_1727,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1717])).

tff(c_1560,plain,(
    ! [C_202,B_203,A_204] :
      ( r2_hidden(C_202,B_203)
      | ~ r2_hidden(C_202,A_204)
      | ~ r1_tarski(A_204,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1803,plain,(
    ! [B_242,B_243,A_244] :
      ( r2_hidden(B_242,B_243)
      | ~ r1_tarski(A_244,B_243)
      | ~ m1_subset_1(B_242,A_244)
      | v1_xboole_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_26,c_1560])).

tff(c_1813,plain,(
    ! [B_242] :
      ( r2_hidden(B_242,'#skF_5')
      | ~ m1_subset_1(B_242,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1727,c_1803])).

tff(c_1837,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,'#skF_5')
      | ~ m1_subset_1(B_245,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1813])).

tff(c_1853,plain,(
    ! [B_245] :
      ( m1_subset_1(B_245,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_245,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1837,c_24])).

tff(c_1865,plain,(
    ! [B_246] :
      ( m1_subset_1(B_246,'#skF_5')
      | ~ m1_subset_1(B_246,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_1853])).

tff(c_1530,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_5')
      | ~ m1_subset_1(B_16,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_1522])).

tff(c_1538,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_5')
      | ~ m1_subset_1(B_16,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1530])).

tff(c_1893,plain,(
    ! [B_247] : ~ m1_subset_1(B_247,'#skF_6') ),
    inference(resolution,[status(thm)],[c_1865,c_1538])).

tff(c_1901,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_107,c_1893])).

tff(c_1912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1901])).

tff(c_1914,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1545])).

tff(c_2096,plain,(
    ! [B_277,A_278] :
      ( r1_tarski(B_277,A_278)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_278))
      | v1_xboole_0(k1_zfmisc_1(A_278)) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_2114,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_2096])).

tff(c_2123,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2114])).

tff(c_1915,plain,(
    ! [C_248,B_249,A_250] :
      ( r2_hidden(C_248,B_249)
      | ~ r2_hidden(C_248,A_250)
      | ~ r1_tarski(A_250,B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1962,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_1'(A_255),B_256)
      | ~ r1_tarski(A_255,B_256)
      | v1_xboole_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_4,c_1915])).

tff(c_1983,plain,(
    ! [B_256,A_255] :
      ( ~ v1_xboole_0(B_256)
      | ~ r1_tarski(A_255,B_256)
      | v1_xboole_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_1962,c_2])).

tff(c_2132,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2123,c_1983])).

tff(c_2135,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_2132])).

tff(c_2137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_2135])).

tff(c_2139,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2147,plain,(
    ! [C_280,A_281] :
      ( r2_hidden(C_280,k1_zfmisc_1(A_281))
      | ~ r1_tarski(C_280,A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2152,plain,(
    ! [A_282,C_283] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_282))
      | ~ r1_tarski(C_283,A_282) ) ),
    inference(resolution,[status(thm)],[c_2147,c_2])).

tff(c_2155,plain,(
    ! [C_283] : ~ r1_tarski(C_283,'#skF_5') ),
    inference(resolution,[status(thm)],[c_2139,c_2152])).

tff(c_2217,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2212,c_2155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.83/1.63  
% 3.83/1.63  %Foreground sorts:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Background operators:
% 3.83/1.63  
% 3.83/1.63  
% 3.83/1.63  %Foreground operators:
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.83/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.83/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.83/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.83/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.83/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.83/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.83/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.83/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.63  
% 3.83/1.66  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.83/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.83/1.66  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 3.83/1.66  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.83/1.66  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.83/1.66  tff(c_2192, plain, (![A_292, B_293]: (r2_hidden('#skF_2'(A_292, B_293), A_292) | r1_tarski(A_292, B_293))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_2212, plain, (![A_294]: (r1_tarski(A_294, A_294))), inference(resolution, [status(thm)], [c_2192, c_8])).
% 3.83/1.66  tff(c_113, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.66  tff(c_127, plain, (![A_43, B_44]: (~v1_xboole_0(A_43) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.83/1.66  tff(c_32, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_131, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_127, c_32])).
% 3.83/1.66  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.66  tff(c_91, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_107, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 3.83/1.66  tff(c_28, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_24, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_124, plain, (![A_41, B_42]: (m1_subset_1('#skF_2'(A_41, B_42), A_41) | v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_113, c_24])).
% 3.83/1.66  tff(c_55, plain, (![D_27]: (r2_hidden(D_27, '#skF_7') | ~r2_hidden(D_27, '#skF_6') | ~m1_subset_1(D_27, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_59, plain, (![D_27]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_27, '#skF_6') | ~m1_subset_1(D_27, '#skF_5'))), inference(resolution, [status(thm)], [c_55, c_2])).
% 3.83/1.66  tff(c_155, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_59])).
% 3.83/1.66  tff(c_34, plain, (![D_21]: (r2_hidden(D_21, '#skF_7') | ~r2_hidden(D_21, '#skF_6') | ~m1_subset_1(D_21, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_106, plain, (![D_21]: (m1_subset_1(D_21, '#skF_7') | v1_xboole_0('#skF_7') | ~r2_hidden(D_21, '#skF_6') | ~m1_subset_1(D_21, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_91])).
% 3.83/1.66  tff(c_204, plain, (![D_57]: (m1_subset_1(D_57, '#skF_7') | ~r2_hidden(D_57, '#skF_6') | ~m1_subset_1(D_57, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_155, c_106])).
% 3.83/1.66  tff(c_220, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_204])).
% 3.83/1.66  tff(c_228, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_131, c_220])).
% 3.83/1.66  tff(c_229, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_228])).
% 3.83/1.66  tff(c_233, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_229])).
% 3.83/1.66  tff(c_234, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_233])).
% 3.83/1.66  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_45, plain, (![B_25, A_26]: (v1_xboole_0(B_25) | ~m1_subset_1(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_52, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_45])).
% 3.83/1.66  tff(c_54, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.83/1.66  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.66  tff(c_81, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_12, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.83/1.66  tff(c_324, plain, (![B_74, A_75]: (r1_tarski(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | v1_xboole_0(k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_345, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_324])).
% 3.83/1.66  tff(c_355, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_345])).
% 3.83/1.66  tff(c_26, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_156, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_517, plain, (![B_97, B_98, A_99]: (r2_hidden(B_97, B_98) | ~r1_tarski(A_99, B_98) | ~m1_subset_1(B_97, A_99) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_26, c_156])).
% 3.83/1.66  tff(c_529, plain, (![B_97]: (r2_hidden(B_97, '#skF_5') | ~m1_subset_1(B_97, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_355, c_517])).
% 3.83/1.66  tff(c_555, plain, (![B_100]: (r2_hidden(B_100, '#skF_5') | ~m1_subset_1(B_100, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_131, c_529])).
% 3.83/1.66  tff(c_568, plain, (![B_100]: (m1_subset_1(B_100, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_100, '#skF_6'))), inference(resolution, [status(thm)], [c_555, c_24])).
% 3.83/1.66  tff(c_610, plain, (![B_103]: (m1_subset_1(B_103, '#skF_5') | ~m1_subset_1(B_103, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_234, c_568])).
% 3.83/1.66  tff(c_628, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_610, c_229])).
% 3.83/1.66  tff(c_632, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_107, c_628])).
% 3.83/1.66  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_632])).
% 3.83/1.66  tff(c_641, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_233])).
% 3.83/1.66  tff(c_731, plain, (![B_120, A_121]: (r1_tarski(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)) | v1_xboole_0(k1_zfmisc_1(A_121)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_749, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_731])).
% 3.83/1.66  tff(c_759, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_749])).
% 3.83/1.66  tff(c_172, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52), B_53) | ~r1_tarski(A_52, B_53) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_4, c_156])).
% 3.83/1.66  tff(c_188, plain, (![B_53, A_52]: (~v1_xboole_0(B_53) | ~r1_tarski(A_52, B_53) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_172, c_2])).
% 3.83/1.66  tff(c_765, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_759, c_188])).
% 3.83/1.66  tff(c_768, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_765])).
% 3.83/1.66  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_768])).
% 3.83/1.66  tff(c_772, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_228])).
% 3.83/1.66  tff(c_30, plain, (![B_16, A_15]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.66  tff(c_796, plain, (v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_772, c_30])).
% 3.83/1.66  tff(c_797, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_796])).
% 3.83/1.66  tff(c_910, plain, (![B_137, A_138]: (r1_tarski(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(A_138)) | v1_xboole_0(k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_931, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_910])).
% 3.83/1.66  tff(c_941, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_931])).
% 3.83/1.66  tff(c_1197, plain, (![B_169, B_170, A_171]: (r2_hidden(B_169, B_170) | ~r1_tarski(A_171, B_170) | ~m1_subset_1(B_169, A_171) | v1_xboole_0(A_171))), inference(resolution, [status(thm)], [c_26, c_156])).
% 3.83/1.66  tff(c_1209, plain, (![B_169]: (r2_hidden(B_169, '#skF_5') | ~m1_subset_1(B_169, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_941, c_1197])).
% 3.83/1.66  tff(c_1238, plain, (![B_172]: (r2_hidden(B_172, '#skF_5') | ~m1_subset_1(B_172, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_131, c_1209])).
% 3.83/1.66  tff(c_1254, plain, (![B_172]: (m1_subset_1(B_172, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_172, '#skF_6'))), inference(resolution, [status(thm)], [c_1238, c_24])).
% 3.83/1.66  tff(c_1294, plain, (![B_174]: (m1_subset_1(B_174, '#skF_5') | ~m1_subset_1(B_174, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_797, c_1254])).
% 3.83/1.66  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_132, plain, (![A_45, B_46]: (~r2_hidden('#skF_2'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_892, plain, (![A_136]: (r1_tarski(A_136, '#skF_7') | ~r2_hidden('#skF_2'(A_136, '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_2'(A_136, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_132])).
% 3.83/1.66  tff(c_896, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_892])).
% 3.83/1.66  tff(c_902, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_896])).
% 3.83/1.66  tff(c_1308, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_1294, c_902])).
% 3.83/1.66  tff(c_1312, plain, (v1_xboole_0('#skF_6') | r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_124, c_1308])).
% 3.83/1.66  tff(c_1319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_131, c_1312])).
% 3.83/1.66  tff(c_1321, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_796])).
% 3.83/1.66  tff(c_1472, plain, (![B_198, A_199]: (r1_tarski(B_198, A_199) | ~m1_subset_1(B_198, k1_zfmisc_1(A_199)) | v1_xboole_0(k1_zfmisc_1(A_199)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_1494, plain, (r1_tarski('#skF_7', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_1472])).
% 3.83/1.66  tff(c_1505, plain, (r1_tarski('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_1494])).
% 3.83/1.66  tff(c_1373, plain, (![D_188, B_189]: (r2_hidden(D_188, B_189) | ~r1_tarski('#skF_7', B_189) | ~r2_hidden(D_188, '#skF_6') | ~m1_subset_1(D_188, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_156])).
% 3.83/1.66  tff(c_1385, plain, (![B_189]: (r2_hidden('#skF_1'('#skF_6'), B_189) | ~r1_tarski('#skF_7', B_189) | ~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_1373])).
% 3.83/1.66  tff(c_1393, plain, (![B_189]: (r2_hidden('#skF_1'('#skF_6'), B_189) | ~r1_tarski('#skF_7', B_189) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_1385])).
% 3.83/1.66  tff(c_1395, plain, (![B_190]: (r2_hidden('#skF_1'('#skF_6'), B_190) | ~r1_tarski('#skF_7', B_190))), inference(negUnitSimplification, [status(thm)], [c_131, c_1393])).
% 3.83/1.66  tff(c_1424, plain, (![B_190]: (~v1_xboole_0(B_190) | ~r1_tarski('#skF_7', B_190))), inference(resolution, [status(thm)], [c_1395, c_2])).
% 3.83/1.66  tff(c_1511, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1505, c_1424])).
% 3.83/1.66  tff(c_1518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1511])).
% 3.83/1.66  tff(c_1522, plain, (![D_200]: (~r2_hidden(D_200, '#skF_6') | ~m1_subset_1(D_200, '#skF_5'))), inference(splitRight, [status(thm)], [c_59])).
% 3.83/1.66  tff(c_1534, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_1522])).
% 3.83/1.66  tff(c_1541, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_131, c_1534])).
% 3.83/1.66  tff(c_1545, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1541])).
% 3.83/1.66  tff(c_1546, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1545])).
% 3.83/1.66  tff(c_1696, plain, (![B_226, A_227]: (r1_tarski(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(A_227)) | v1_xboole_0(k1_zfmisc_1(A_227)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_1717, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_1696])).
% 3.83/1.66  tff(c_1727, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_1717])).
% 3.83/1.66  tff(c_1560, plain, (![C_202, B_203, A_204]: (r2_hidden(C_202, B_203) | ~r2_hidden(C_202, A_204) | ~r1_tarski(A_204, B_203))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_1803, plain, (![B_242, B_243, A_244]: (r2_hidden(B_242, B_243) | ~r1_tarski(A_244, B_243) | ~m1_subset_1(B_242, A_244) | v1_xboole_0(A_244))), inference(resolution, [status(thm)], [c_26, c_1560])).
% 3.83/1.66  tff(c_1813, plain, (![B_242]: (r2_hidden(B_242, '#skF_5') | ~m1_subset_1(B_242, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_1727, c_1803])).
% 3.83/1.66  tff(c_1837, plain, (![B_245]: (r2_hidden(B_245, '#skF_5') | ~m1_subset_1(B_245, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_131, c_1813])).
% 3.83/1.66  tff(c_1853, plain, (![B_245]: (m1_subset_1(B_245, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_245, '#skF_6'))), inference(resolution, [status(thm)], [c_1837, c_24])).
% 3.83/1.66  tff(c_1865, plain, (![B_246]: (m1_subset_1(B_246, '#skF_5') | ~m1_subset_1(B_246, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1546, c_1853])).
% 3.83/1.66  tff(c_1530, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_5') | ~m1_subset_1(B_16, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_1522])).
% 3.83/1.66  tff(c_1538, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_5') | ~m1_subset_1(B_16, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_131, c_1530])).
% 3.83/1.66  tff(c_1893, plain, (![B_247]: (~m1_subset_1(B_247, '#skF_6'))), inference(resolution, [status(thm)], [c_1865, c_1538])).
% 3.83/1.66  tff(c_1901, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_107, c_1893])).
% 3.83/1.66  tff(c_1912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_1901])).
% 3.83/1.66  tff(c_1914, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1545])).
% 3.83/1.66  tff(c_2096, plain, (![B_277, A_278]: (r1_tarski(B_277, A_278) | ~m1_subset_1(B_277, k1_zfmisc_1(A_278)) | v1_xboole_0(k1_zfmisc_1(A_278)))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.83/1.66  tff(c_2114, plain, (r1_tarski('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_2096])).
% 3.83/1.66  tff(c_2123, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_2114])).
% 3.83/1.66  tff(c_1915, plain, (![C_248, B_249, A_250]: (r2_hidden(C_248, B_249) | ~r2_hidden(C_248, A_250) | ~r1_tarski(A_250, B_249))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.83/1.66  tff(c_1962, plain, (![A_255, B_256]: (r2_hidden('#skF_1'(A_255), B_256) | ~r1_tarski(A_255, B_256) | v1_xboole_0(A_255))), inference(resolution, [status(thm)], [c_4, c_1915])).
% 3.83/1.66  tff(c_1983, plain, (![B_256, A_255]: (~v1_xboole_0(B_256) | ~r1_tarski(A_255, B_256) | v1_xboole_0(A_255))), inference(resolution, [status(thm)], [c_1962, c_2])).
% 3.83/1.66  tff(c_2132, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2123, c_1983])).
% 3.83/1.66  tff(c_2135, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_2132])).
% 3.83/1.66  tff(c_2137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_2135])).
% 3.83/1.66  tff(c_2139, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 3.83/1.66  tff(c_2147, plain, (![C_280, A_281]: (r2_hidden(C_280, k1_zfmisc_1(A_281)) | ~r1_tarski(C_280, A_281))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.83/1.66  tff(c_2152, plain, (![A_282, C_283]: (~v1_xboole_0(k1_zfmisc_1(A_282)) | ~r1_tarski(C_283, A_282))), inference(resolution, [status(thm)], [c_2147, c_2])).
% 3.83/1.66  tff(c_2155, plain, (![C_283]: (~r1_tarski(C_283, '#skF_5'))), inference(resolution, [status(thm)], [c_2139, c_2152])).
% 3.83/1.66  tff(c_2217, plain, $false, inference(resolution, [status(thm)], [c_2212, c_2155])).
% 3.83/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.66  
% 3.83/1.66  Inference rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Ref     : 0
% 3.83/1.66  #Sup     : 443
% 3.83/1.66  #Fact    : 0
% 3.83/1.66  #Define  : 0
% 3.83/1.66  #Split   : 8
% 3.83/1.66  #Chain   : 0
% 3.83/1.66  #Close   : 0
% 3.83/1.66  
% 3.83/1.66  Ordering : KBO
% 3.83/1.66  
% 3.83/1.66  Simplification rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Subsume      : 109
% 3.83/1.66  #Demod        : 42
% 3.83/1.66  #Tautology    : 51
% 3.83/1.66  #SimpNegUnit  : 65
% 3.83/1.66  #BackRed      : 0
% 3.83/1.66  
% 3.83/1.66  #Partial instantiations: 0
% 3.83/1.66  #Strategies tried      : 1
% 3.83/1.66  
% 3.83/1.66  Timing (in seconds)
% 3.83/1.66  ----------------------
% 3.83/1.66  Preprocessing        : 0.27
% 3.83/1.66  Parsing              : 0.15
% 3.83/1.66  CNF conversion       : 0.02
% 3.83/1.66  Main loop            : 0.59
% 3.83/1.66  Inferencing          : 0.23
% 3.83/1.66  Reduction            : 0.14
% 3.83/1.66  Demodulation         : 0.09
% 3.83/1.66  BG Simplification    : 0.03
% 3.83/1.66  Subsumption          : 0.13
% 3.83/1.66  Abstraction          : 0.03
% 3.83/1.66  MUC search           : 0.00
% 3.83/1.66  Cooper               : 0.00
% 3.83/1.66  Total                : 0.91
% 3.83/1.66  Index Insertion      : 0.00
% 3.83/1.66  Index Deletion       : 0.00
% 3.83/1.66  Index Matching       : 0.00
% 3.83/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
