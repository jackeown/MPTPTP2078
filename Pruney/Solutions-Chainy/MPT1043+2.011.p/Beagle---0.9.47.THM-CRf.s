%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 799 expanded)
%              Number of leaves         :   27 ( 275 expanded)
%              Depth                    :   18
%              Number of atoms          :  249 (1966 expanded)
%              Number of equality atoms :   16 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k5_partfun1(A,B,C),k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B)
        & v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => v1_xboole_0(k5_partfun1(A,B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_47,c_4])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [D_62,A_63,B_64,C_65] :
      ( v1_funct_1(D_62)
      | ~ r2_hidden(D_62,k5_partfun1(A_63,B_64,C_65))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_478,plain,(
    ! [A_138,B_139,C_140,B_141] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_138,B_139,C_140),B_141))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140)
      | r1_tarski(k5_partfun1(A_138,B_139,C_140),B_141) ) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_483,plain,(
    ! [B_141] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_141))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_141) ) ),
    inference(resolution,[status(thm)],[c_32,c_478])).

tff(c_487,plain,(
    ! [B_141] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_141))
      | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_483])).

tff(c_72,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_1,B_2,B_40] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_40)
      | ~ r1_tarski(A_1,B_40)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_354,plain,(
    ! [D_106,A_107,B_108,C_109] :
      ( v1_funct_2(D_106,A_107,B_108)
      | ~ r2_hidden(D_106,k5_partfun1(A_107,B_108,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_647,plain,(
    ! [A_195,B_194,A_196,B_193,C_192] :
      ( v1_funct_2('#skF_1'(A_195,B_194),A_196,B_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_196,B_193)))
      | ~ v1_funct_1(C_192)
      | ~ r1_tarski(A_195,k5_partfun1(A_196,B_193,C_192))
      | r1_tarski(A_195,B_194) ) ),
    inference(resolution,[status(thm)],[c_75,c_354])).

tff(c_654,plain,(
    ! [A_195,B_194] :
      ( v1_funct_2('#skF_1'(A_195,B_194),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_195,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_195,B_194) ) ),
    inference(resolution,[status(thm)],[c_32,c_647])).

tff(c_659,plain,(
    ! [A_195,B_194] :
      ( v1_funct_2('#skF_1'(A_195,B_194),'#skF_2','#skF_3')
      | ~ r1_tarski(A_195,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_195,B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_654])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [C_33,B_34,A_35] :
      ( ~ v1_xboole_0(C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [B_36,A_37,A_38] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_37,A_38)
      | ~ r1_tarski(A_38,B_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_76,plain,(
    ! [B_42,A_43,B_44] :
      ( ~ v1_xboole_0(B_42)
      | ~ r1_tarski(A_43,B_42)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_83,plain,(
    ! [A_45,B_46] :
      ( ~ v1_xboole_0(A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_94,plain,(
    ~ v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_83,c_30])).

tff(c_243,plain,(
    ! [A_77,B_78,C_79] :
      ( v1_xboole_0(k5_partfun1(A_77,B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79)
      | ~ v1_xboole_0(B_78)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_250,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_243])).

tff(c_254,plain,
    ( v1_xboole_0(k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_250])).

tff(c_255,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_254])).

tff(c_256,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_406,plain,(
    ! [D_121,A_122,B_123,C_124] :
      ( m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ r2_hidden(D_121,k5_partfun1(A_122,B_123,C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_804,plain,(
    ! [C_226,A_224,B_225,A_222,B_223] :
      ( m1_subset_1('#skF_1'(A_224,B_223),k1_zfmisc_1(k2_zfmisc_1(A_222,B_225)))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_222,B_225)))
      | ~ v1_funct_1(C_226)
      | ~ r1_tarski(A_224,k5_partfun1(A_222,B_225,C_226))
      | r1_tarski(A_224,B_223) ) ),
    inference(resolution,[status(thm)],[c_75,c_406])).

tff(c_811,plain,(
    ! [A_224,B_223] :
      ( m1_subset_1('#skF_1'(A_224,B_223),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_224,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_224,B_223) ) ),
    inference(resolution,[status(thm)],[c_32,c_804])).

tff(c_817,plain,(
    ! [A_227,B_228] :
      ( m1_subset_1('#skF_1'(A_227,B_228),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_227,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_227,B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_811])).

tff(c_22,plain,(
    ! [B_16,C_17,A_15] :
      ( k1_xboole_0 = B_16
      | r2_hidden(C_17,k1_funct_2(A_15,B_16))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_841,plain,(
    ! [A_227,B_228] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden('#skF_1'(A_227,B_228),k1_funct_2('#skF_2','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_227,B_228),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_227,B_228))
      | ~ r1_tarski(A_227,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_817,c_22])).

tff(c_1249,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_841])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1281,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_8])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_1281])).

tff(c_1285,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_841])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_844,plain,(
    ! [A_227,B_228] :
      ( r1_tarski('#skF_1'(A_227,B_228),k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_227,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_227,B_228) ) ),
    inference(resolution,[status(thm)],[c_817,c_12])).

tff(c_392,plain,(
    ! [B_117,C_118,A_119] :
      ( k1_xboole_0 = B_117
      | r2_hidden(C_118,k1_funct_2(A_119,B_117))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117)))
      | ~ v1_funct_2(C_118,A_119,B_117)
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_419,plain,(
    ! [B_125,A_126,A_127] :
      ( k1_xboole_0 = B_125
      | r2_hidden(A_126,k1_funct_2(A_127,B_125))
      | ~ v1_funct_2(A_126,A_127,B_125)
      | ~ v1_funct_1(A_126)
      | ~ r1_tarski(A_126,k2_zfmisc_1(A_127,B_125)) ) ),
    inference(resolution,[status(thm)],[c_14,c_392])).

tff(c_1576,plain,(
    ! [A_303,A_304,B_305] :
      ( r1_tarski(A_303,k1_funct_2(A_304,B_305))
      | k1_xboole_0 = B_305
      | ~ v1_funct_2('#skF_1'(A_303,k1_funct_2(A_304,B_305)),A_304,B_305)
      | ~ v1_funct_1('#skF_1'(A_303,k1_funct_2(A_304,B_305)))
      | ~ r1_tarski('#skF_1'(A_303,k1_funct_2(A_304,B_305)),k2_zfmisc_1(A_304,B_305)) ) ),
    inference(resolution,[status(thm)],[c_419,c_4])).

tff(c_1592,plain,(
    ! [A_227] :
      ( k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_1'(A_227,k1_funct_2('#skF_2','#skF_3')),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_227,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_227,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_227,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_844,c_1576])).

tff(c_1615,plain,(
    ! [A_306] :
      ( ~ v1_funct_2('#skF_1'(A_306,k1_funct_2('#skF_2','#skF_3')),'#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_306,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_306,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_306,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1285,c_1592])).

tff(c_1631,plain,(
    ! [A_307] :
      ( ~ v1_funct_1('#skF_1'(A_307,k1_funct_2('#skF_2','#skF_3')))
      | ~ r1_tarski(A_307,k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | r1_tarski(A_307,k1_funct_2('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_659,c_1615])).

tff(c_1639,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_487,c_1631])).

tff(c_1643,plain,(
    r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k1_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1639])).

tff(c_1645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1643])).

tff(c_1647,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_83,c_10])).

tff(c_1655,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1647,c_95])).

tff(c_1646,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_1651,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1646,c_95])).

tff(c_1664,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_1651])).

tff(c_1680,plain,(
    ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1664,c_30])).

tff(c_1682,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_32])).

tff(c_2023,plain,(
    ! [A_369,B_370,C_371,B_372] :
      ( v1_funct_1('#skF_1'(k5_partfun1(A_369,B_370,C_371),B_372))
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370)))
      | ~ v1_funct_1(C_371)
      | r1_tarski(k5_partfun1(A_369,B_370,C_371),B_372) ) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_2025,plain,(
    ! [B_372] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_372))
      | ~ v1_funct_1('#skF_4')
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_372) ) ),
    inference(resolution,[status(thm)],[c_1682,c_2023])).

tff(c_2031,plain,(
    ! [B_372] :
      ( v1_funct_1('#skF_1'(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_372))
      | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),B_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2025])).

tff(c_1780,plain,(
    ! [D_314,A_315,B_316,C_317] :
      ( v1_funct_2(D_314,A_315,B_316)
      | ~ r2_hidden(D_314,k5_partfun1(A_315,B_316,C_317))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ v1_funct_1(C_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2253,plain,(
    ! [B_438,B_440,C_437,A_436,A_439] :
      ( v1_funct_2('#skF_1'(A_439,B_438),A_436,B_440)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_436,B_440)))
      | ~ v1_funct_1(C_437)
      | ~ r1_tarski(A_439,k5_partfun1(A_436,B_440,C_437))
      | r1_tarski(A_439,B_438) ) ),
    inference(resolution,[status(thm)],[c_75,c_1780])).

tff(c_2257,plain,(
    ! [A_439,B_438] :
      ( v1_funct_2('#skF_1'(A_439,B_438),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_439,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_439,B_438) ) ),
    inference(resolution,[status(thm)],[c_1682,c_2253])).

tff(c_2264,plain,(
    ! [A_439,B_438] :
      ( v1_funct_2('#skF_1'(A_439,B_438),'#skF_3','#skF_3')
      | ~ r1_tarski(A_439,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_439,B_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2257])).

tff(c_1947,plain,(
    ! [D_350,A_351,B_352,C_353] :
      ( m1_subset_1(D_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ r2_hidden(D_350,k5_partfun1(A_351,B_352,C_353))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2413,plain,(
    ! [A_470,B_468,B_469,C_466,A_467] :
      ( m1_subset_1('#skF_1'(A_470,B_469),k1_zfmisc_1(k2_zfmisc_1(A_467,B_468)))
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468)))
      | ~ v1_funct_1(C_466)
      | ~ r1_tarski(A_470,k5_partfun1(A_467,B_468,C_466))
      | r1_tarski(A_470,B_469) ) ),
    inference(resolution,[status(thm)],[c_75,c_1947])).

tff(c_2417,plain,(
    ! [A_470,B_469] :
      ( m1_subset_1('#skF_1'(A_470,B_469),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(A_470,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_470,B_469) ) ),
    inference(resolution,[status(thm)],[c_1682,c_2413])).

tff(c_2426,plain,(
    ! [A_471,B_472] :
      ( m1_subset_1('#skF_1'(A_471,B_472),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ r1_tarski(A_471,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_471,B_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2417])).

tff(c_20,plain,(
    ! [C_17,B_16] :
      ( r2_hidden(C_17,k1_funct_2(k1_xboole_0,B_16))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16)))
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1695,plain,(
    ! [C_17,B_16] :
      ( r2_hidden(C_17,k1_funct_2('#skF_3',B_16))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_16)))
      | ~ v1_funct_2(C_17,'#skF_3',B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_1655,c_1655,c_20])).

tff(c_2640,plain,(
    ! [A_500,B_501] :
      ( r2_hidden('#skF_1'(A_500,B_501),k1_funct_2('#skF_3','#skF_3'))
      | ~ v1_funct_2('#skF_1'(A_500,B_501),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_500,B_501))
      | ~ r1_tarski(A_500,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_500,B_501) ) ),
    inference(resolution,[status(thm)],[c_2426,c_1695])).

tff(c_3049,plain,(
    ! [A_536] :
      ( ~ v1_funct_2('#skF_1'(A_536,k1_funct_2('#skF_3','#skF_3')),'#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_1'(A_536,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_536,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_536,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2640,c_4])).

tff(c_3065,plain,(
    ! [A_537] :
      ( ~ v1_funct_1('#skF_1'(A_537,k1_funct_2('#skF_3','#skF_3')))
      | ~ r1_tarski(A_537,k5_partfun1('#skF_3','#skF_3','#skF_4'))
      | r1_tarski(A_537,k1_funct_2('#skF_3','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2264,c_3049])).

tff(c_3073,plain,
    ( ~ r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k5_partfun1('#skF_3','#skF_3','#skF_4'))
    | r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2031,c_3065])).

tff(c_3077,plain,(
    r1_tarski(k5_partfun1('#skF_3','#skF_3','#skF_4'),k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3073])).

tff(c_3079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1680,c_3077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:17:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.21  
% 6.00/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.21  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.00/2.21  
% 6.00/2.21  %Foreground sorts:
% 6.00/2.21  
% 6.00/2.21  
% 6.00/2.21  %Background operators:
% 6.00/2.21  
% 6.00/2.21  
% 6.00/2.21  %Foreground operators:
% 6.00/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.21  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.21  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.21  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 6.00/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.21  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.21  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 6.00/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.00/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.00/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.21  
% 6.32/2.23  tff(f_91, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k5_partfun1(A, B, C), k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_2)).
% 6.32/2.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.32/2.23  tff(f_84, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_2)).
% 6.32/2.23  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.32/2.23  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.32/2.23  tff(f_59, axiom, (![A, B, C]: ((((~v1_xboole_0(A) & v1_xboole_0(B)) & v1_funct_1(C)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => v1_xboole_0(k5_partfun1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_partfun1)).
% 6.32/2.23  tff(f_71, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 6.32/2.23  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.32/2.23  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.32/2.23  tff(c_30, plain, (~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.32/2.23  tff(c_47, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.32/2.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.32/2.23  tff(c_52, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_47, c_4])).
% 6.32/2.23  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.32/2.23  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.32/2.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.32/2.23  tff(c_156, plain, (![D_62, A_63, B_64, C_65]: (v1_funct_1(D_62) | ~r2_hidden(D_62, k5_partfun1(A_63, B_64, C_65)) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.32/2.23  tff(c_478, plain, (![A_138, B_139, C_140, B_141]: (v1_funct_1('#skF_1'(k5_partfun1(A_138, B_139, C_140), B_141)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140) | r1_tarski(k5_partfun1(A_138, B_139, C_140), B_141))), inference(resolution, [status(thm)], [c_6, c_156])).
% 6.32/2.23  tff(c_483, plain, (![B_141]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_141)) | ~v1_funct_1('#skF_4') | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_141))), inference(resolution, [status(thm)], [c_32, c_478])).
% 6.32/2.23  tff(c_487, plain, (![B_141]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_141)) | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), B_141))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_483])).
% 6.32/2.23  tff(c_72, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.32/2.23  tff(c_75, plain, (![A_1, B_2, B_40]: (r2_hidden('#skF_1'(A_1, B_2), B_40) | ~r1_tarski(A_1, B_40) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_72])).
% 6.32/2.23  tff(c_354, plain, (![D_106, A_107, B_108, C_109]: (v1_funct_2(D_106, A_107, B_108) | ~r2_hidden(D_106, k5_partfun1(A_107, B_108, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.32/2.23  tff(c_647, plain, (![A_195, B_194, A_196, B_193, C_192]: (v1_funct_2('#skF_1'(A_195, B_194), A_196, B_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_196, B_193))) | ~v1_funct_1(C_192) | ~r1_tarski(A_195, k5_partfun1(A_196, B_193, C_192)) | r1_tarski(A_195, B_194))), inference(resolution, [status(thm)], [c_75, c_354])).
% 6.32/2.23  tff(c_654, plain, (![A_195, B_194]: (v1_funct_2('#skF_1'(A_195, B_194), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~r1_tarski(A_195, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_195, B_194))), inference(resolution, [status(thm)], [c_32, c_647])).
% 6.32/2.23  tff(c_659, plain, (![A_195, B_194]: (v1_funct_2('#skF_1'(A_195, B_194), '#skF_2', '#skF_3') | ~r1_tarski(A_195, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_195, B_194))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_654])).
% 6.32/2.23  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.32/2.23  tff(c_60, plain, (![C_33, B_34, A_35]: (~v1_xboole_0(C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.32/2.23  tff(c_68, plain, (![B_36, A_37, A_38]: (~v1_xboole_0(B_36) | ~r2_hidden(A_37, A_38) | ~r1_tarski(A_38, B_36))), inference(resolution, [status(thm)], [c_14, c_60])).
% 6.32/2.23  tff(c_76, plain, (![B_42, A_43, B_44]: (~v1_xboole_0(B_42) | ~r1_tarski(A_43, B_42) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_68])).
% 6.32/2.23  tff(c_83, plain, (![A_45, B_46]: (~v1_xboole_0(A_45) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_52, c_76])).
% 6.32/2.23  tff(c_94, plain, (~v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_30])).
% 6.32/2.23  tff(c_243, plain, (![A_77, B_78, C_79]: (v1_xboole_0(k5_partfun1(A_77, B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79) | ~v1_xboole_0(B_78) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.32/2.23  tff(c_250, plain, (v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_243])).
% 6.32/2.23  tff(c_254, plain, (v1_xboole_0(k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_250])).
% 6.32/2.23  tff(c_255, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_254])).
% 6.32/2.23  tff(c_256, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_255])).
% 6.32/2.23  tff(c_406, plain, (![D_121, A_122, B_123, C_124]: (m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~r2_hidden(D_121, k5_partfun1(A_122, B_123, C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.32/2.23  tff(c_804, plain, (![C_226, A_224, B_225, A_222, B_223]: (m1_subset_1('#skF_1'(A_224, B_223), k1_zfmisc_1(k2_zfmisc_1(A_222, B_225))) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_222, B_225))) | ~v1_funct_1(C_226) | ~r1_tarski(A_224, k5_partfun1(A_222, B_225, C_226)) | r1_tarski(A_224, B_223))), inference(resolution, [status(thm)], [c_75, c_406])).
% 6.32/2.23  tff(c_811, plain, (![A_224, B_223]: (m1_subset_1('#skF_1'(A_224, B_223), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(A_224, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_224, B_223))), inference(resolution, [status(thm)], [c_32, c_804])).
% 6.32/2.23  tff(c_817, plain, (![A_227, B_228]: (m1_subset_1('#skF_1'(A_227, B_228), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_227, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_227, B_228))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_811])).
% 6.32/2.23  tff(c_22, plain, (![B_16, C_17, A_15]: (k1_xboole_0=B_16 | r2_hidden(C_17, k1_funct_2(A_15, B_16)) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.32/2.23  tff(c_841, plain, (![A_227, B_228]: (k1_xboole_0='#skF_3' | r2_hidden('#skF_1'(A_227, B_228), k1_funct_2('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_1'(A_227, B_228), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_227, B_228)) | ~r1_tarski(A_227, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_227, B_228))), inference(resolution, [status(thm)], [c_817, c_22])).
% 6.32/2.23  tff(c_1249, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_841])).
% 6.32/2.23  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.32/2.23  tff(c_1281, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_8])).
% 6.32/2.23  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_1281])).
% 6.32/2.23  tff(c_1285, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_841])).
% 6.32/2.23  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.32/2.23  tff(c_844, plain, (![A_227, B_228]: (r1_tarski('#skF_1'(A_227, B_228), k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_227, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_227, B_228))), inference(resolution, [status(thm)], [c_817, c_12])).
% 6.32/2.23  tff(c_392, plain, (![B_117, C_118, A_119]: (k1_xboole_0=B_117 | r2_hidden(C_118, k1_funct_2(A_119, B_117)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))) | ~v1_funct_2(C_118, A_119, B_117) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.32/2.23  tff(c_419, plain, (![B_125, A_126, A_127]: (k1_xboole_0=B_125 | r2_hidden(A_126, k1_funct_2(A_127, B_125)) | ~v1_funct_2(A_126, A_127, B_125) | ~v1_funct_1(A_126) | ~r1_tarski(A_126, k2_zfmisc_1(A_127, B_125)))), inference(resolution, [status(thm)], [c_14, c_392])).
% 6.32/2.23  tff(c_1576, plain, (![A_303, A_304, B_305]: (r1_tarski(A_303, k1_funct_2(A_304, B_305)) | k1_xboole_0=B_305 | ~v1_funct_2('#skF_1'(A_303, k1_funct_2(A_304, B_305)), A_304, B_305) | ~v1_funct_1('#skF_1'(A_303, k1_funct_2(A_304, B_305))) | ~r1_tarski('#skF_1'(A_303, k1_funct_2(A_304, B_305)), k2_zfmisc_1(A_304, B_305)))), inference(resolution, [status(thm)], [c_419, c_4])).
% 6.32/2.23  tff(c_1592, plain, (![A_227]: (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_1'(A_227, k1_funct_2('#skF_2', '#skF_3')), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_227, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_227, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_227, k1_funct_2('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_844, c_1576])).
% 6.32/2.23  tff(c_1615, plain, (![A_306]: (~v1_funct_2('#skF_1'(A_306, k1_funct_2('#skF_2', '#skF_3')), '#skF_2', '#skF_3') | ~v1_funct_1('#skF_1'(A_306, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_306, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_306, k1_funct_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1285, c_1592])).
% 6.32/2.23  tff(c_1631, plain, (![A_307]: (~v1_funct_1('#skF_1'(A_307, k1_funct_2('#skF_2', '#skF_3'))) | ~r1_tarski(A_307, k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(A_307, k1_funct_2('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_659, c_1615])).
% 6.32/2.23  tff(c_1639, plain, (~r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k5_partfun1('#skF_2', '#skF_3', '#skF_4')) | r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_487, c_1631])).
% 6.32/2.23  tff(c_1643, plain, (r1_tarski(k5_partfun1('#skF_2', '#skF_3', '#skF_4'), k1_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1639])).
% 6.32/2.23  tff(c_1645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1643])).
% 6.32/2.23  tff(c_1647, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_255])).
% 6.32/2.23  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.32/2.23  tff(c_95, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_83, c_10])).
% 6.32/2.23  tff(c_1655, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1647, c_95])).
% 6.32/2.23  tff(c_1646, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_255])).
% 6.32/2.23  tff(c_1651, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1646, c_95])).
% 6.32/2.23  tff(c_1664, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_1651])).
% 6.32/2.23  tff(c_1680, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1664, c_30])).
% 6.32/2.23  tff(c_1682, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_32])).
% 6.32/2.23  tff(c_2023, plain, (![A_369, B_370, C_371, B_372]: (v1_funct_1('#skF_1'(k5_partfun1(A_369, B_370, C_371), B_372)) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))) | ~v1_funct_1(C_371) | r1_tarski(k5_partfun1(A_369, B_370, C_371), B_372))), inference(resolution, [status(thm)], [c_6, c_156])).
% 6.32/2.23  tff(c_2025, plain, (![B_372]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_372)) | ~v1_funct_1('#skF_4') | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_372))), inference(resolution, [status(thm)], [c_1682, c_2023])).
% 6.32/2.23  tff(c_2031, plain, (![B_372]: (v1_funct_1('#skF_1'(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_372)) | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), B_372))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2025])).
% 6.32/2.23  tff(c_1780, plain, (![D_314, A_315, B_316, C_317]: (v1_funct_2(D_314, A_315, B_316) | ~r2_hidden(D_314, k5_partfun1(A_315, B_316, C_317)) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~v1_funct_1(C_317))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.32/2.23  tff(c_2253, plain, (![B_438, B_440, C_437, A_436, A_439]: (v1_funct_2('#skF_1'(A_439, B_438), A_436, B_440) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_436, B_440))) | ~v1_funct_1(C_437) | ~r1_tarski(A_439, k5_partfun1(A_436, B_440, C_437)) | r1_tarski(A_439, B_438))), inference(resolution, [status(thm)], [c_75, c_1780])).
% 6.32/2.23  tff(c_2257, plain, (![A_439, B_438]: (v1_funct_2('#skF_1'(A_439, B_438), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~r1_tarski(A_439, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_439, B_438))), inference(resolution, [status(thm)], [c_1682, c_2253])).
% 6.32/2.23  tff(c_2264, plain, (![A_439, B_438]: (v1_funct_2('#skF_1'(A_439, B_438), '#skF_3', '#skF_3') | ~r1_tarski(A_439, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_439, B_438))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2257])).
% 6.32/2.23  tff(c_1947, plain, (![D_350, A_351, B_352, C_353]: (m1_subset_1(D_350, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~r2_hidden(D_350, k5_partfun1(A_351, B_352, C_353)) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_1(C_353))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.32/2.23  tff(c_2413, plain, (![A_470, B_468, B_469, C_466, A_467]: (m1_subset_1('#skF_1'(A_470, B_469), k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))) | ~v1_funct_1(C_466) | ~r1_tarski(A_470, k5_partfun1(A_467, B_468, C_466)) | r1_tarski(A_470, B_469))), inference(resolution, [status(thm)], [c_75, c_1947])).
% 6.32/2.23  tff(c_2417, plain, (![A_470, B_469]: (m1_subset_1('#skF_1'(A_470, B_469), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(A_470, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_470, B_469))), inference(resolution, [status(thm)], [c_1682, c_2413])).
% 6.32/2.23  tff(c_2426, plain, (![A_471, B_472]: (m1_subset_1('#skF_1'(A_471, B_472), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~r1_tarski(A_471, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_471, B_472))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2417])).
% 6.32/2.23  tff(c_20, plain, (![C_17, B_16]: (r2_hidden(C_17, k1_funct_2(k1_xboole_0, B_16)) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))) | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.32/2.23  tff(c_1695, plain, (![C_17, B_16]: (r2_hidden(C_17, k1_funct_2('#skF_3', B_16)) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_16))) | ~v1_funct_2(C_17, '#skF_3', B_16) | ~v1_funct_1(C_17))), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_1655, c_1655, c_20])).
% 6.32/2.23  tff(c_2640, plain, (![A_500, B_501]: (r2_hidden('#skF_1'(A_500, B_501), k1_funct_2('#skF_3', '#skF_3')) | ~v1_funct_2('#skF_1'(A_500, B_501), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_1'(A_500, B_501)) | ~r1_tarski(A_500, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_500, B_501))), inference(resolution, [status(thm)], [c_2426, c_1695])).
% 6.32/2.23  tff(c_3049, plain, (![A_536]: (~v1_funct_2('#skF_1'(A_536, k1_funct_2('#skF_3', '#skF_3')), '#skF_3', '#skF_3') | ~v1_funct_1('#skF_1'(A_536, k1_funct_2('#skF_3', '#skF_3'))) | ~r1_tarski(A_536, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_536, k1_funct_2('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_2640, c_4])).
% 6.32/2.23  tff(c_3065, plain, (![A_537]: (~v1_funct_1('#skF_1'(A_537, k1_funct_2('#skF_3', '#skF_3'))) | ~r1_tarski(A_537, k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(A_537, k1_funct_2('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_2264, c_3049])).
% 6.32/2.23  tff(c_3073, plain, (~r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k5_partfun1('#skF_3', '#skF_3', '#skF_4')) | r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_2031, c_3065])).
% 6.32/2.23  tff(c_3077, plain, (r1_tarski(k5_partfun1('#skF_3', '#skF_3', '#skF_4'), k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3073])).
% 6.32/2.23  tff(c_3079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1680, c_3077])).
% 6.32/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.23  
% 6.32/2.23  Inference rules
% 6.32/2.23  ----------------------
% 6.32/2.23  #Ref     : 0
% 6.32/2.23  #Sup     : 736
% 6.32/2.23  #Fact    : 0
% 6.32/2.23  #Define  : 0
% 6.32/2.23  #Split   : 16
% 6.32/2.23  #Chain   : 0
% 6.32/2.23  #Close   : 0
% 6.32/2.23  
% 6.32/2.23  Ordering : KBO
% 6.32/2.23  
% 6.32/2.23  Simplification rules
% 6.32/2.23  ----------------------
% 6.32/2.23  #Subsume      : 220
% 6.32/2.23  #Demod        : 166
% 6.32/2.23  #Tautology    : 48
% 6.32/2.23  #SimpNegUnit  : 11
% 6.32/2.23  #BackRed      : 50
% 6.32/2.23  
% 6.32/2.23  #Partial instantiations: 0
% 6.32/2.23  #Strategies tried      : 1
% 6.32/2.23  
% 6.32/2.23  Timing (in seconds)
% 6.32/2.23  ----------------------
% 6.32/2.24  Preprocessing        : 0.30
% 6.32/2.24  Parsing              : 0.16
% 6.32/2.24  CNF conversion       : 0.02
% 6.32/2.24  Main loop            : 1.17
% 6.32/2.24  Inferencing          : 0.39
% 6.32/2.24  Reduction            : 0.28
% 6.32/2.24  Demodulation         : 0.18
% 6.32/2.24  BG Simplification    : 0.04
% 6.32/2.24  Subsumption          : 0.38
% 6.32/2.24  Abstraction          : 0.04
% 6.32/2.24  MUC search           : 0.00
% 6.32/2.24  Cooper               : 0.00
% 6.32/2.24  Total                : 1.52
% 6.32/2.24  Index Insertion      : 0.00
% 6.32/2.24  Index Deletion       : 0.00
% 6.32/2.24  Index Matching       : 0.00
% 6.32/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
