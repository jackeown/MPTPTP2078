%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 20.45s
% Output     : CNFRefutation 20.55s
% Verified   : 
% Statistics : Number of formulae       :  134 (1192 expanded)
%              Number of leaves         :   24 ( 398 expanded)
%              Depth                    :   28
%              Number of atoms          :  264 (2934 expanded)
%              Number of equality atoms :   44 ( 327 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_26,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_143,plain,(
    ! [A_56,C_57,B_58] :
      ( m1_subset_1(A_56,C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_153,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_59,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_32,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_6')
      | ~ r2_hidden(D_26,'#skF_7')
      | ~ m1_subset_1(D_26,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_169,plain,(
    ! [A_60] :
      ( r2_hidden(A_60,'#skF_6')
      | ~ r2_hidden(A_60,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_153,c_32])).

tff(c_55542,plain,(
    ! [B_1503] :
      ( r2_hidden('#skF_2'('#skF_7',B_1503),'#skF_6')
      | r1_tarski('#skF_7',B_1503) ) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55563,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_55542,c_8])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1('#skF_4'(A_12,B_13),A_12)
      | B_13 = A_12
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_523,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_2'('#skF_7',B_80),'#skF_6')
      | r1_tarski('#skF_7',B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_538,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_523,c_8])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_231,plain,(
    ! [A_62] :
      ( m1_subset_1(A_62,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_34,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_7')
      | ~ r2_hidden(D_26,'#skF_6')
      | ~ m1_subset_1(D_26,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_243,plain,(
    ! [A_63] :
      ( r2_hidden(A_63,'#skF_7')
      | ~ r2_hidden(A_63,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_231,c_34])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_63] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_63,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_264,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_78,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_41] : r1_tarski(A_41,A_41) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_595,plain,(
    ! [A_84,B_85,A_86] :
      ( m1_subset_1(A_84,B_85)
      | ~ r2_hidden(A_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_789,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1('#skF_1'(A_100),B_101)
      | ~ r1_tarski(A_100,B_101)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_4,c_595])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5328,plain,(
    ! [A_270,B_271] :
      ( r1_tarski('#skF_1'(A_270),B_271)
      | ~ r1_tarski(A_270,k1_zfmisc_1(B_271))
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_789,c_20])).

tff(c_88,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54),B_55)
      | ~ r1_tarski(A_54,B_55)
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_142,plain,(
    ! [B_55,A_54] :
      ( ~ v1_xboole_0(B_55)
      | ~ r1_tarski(A_54,B_55)
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_18298,plain,(
    ! [B_571,A_572] :
      ( ~ v1_xboole_0(B_571)
      | v1_xboole_0('#skF_1'(A_572))
      | ~ r1_tarski(A_572,k1_zfmisc_1(B_571))
      | v1_xboole_0(A_572) ) ),
    inference(resolution,[status(thm)],[c_5328,c_142])).

tff(c_18400,plain,(
    ! [B_573] :
      ( ~ v1_xboole_0(B_573)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(B_573)))
      | v1_xboole_0(k1_zfmisc_1(B_573)) ) ),
    inference(resolution,[status(thm)],[c_86,c_18298])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,'#skF_5')
      | ~ r2_hidden(A_61,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_153,c_20])).

tff(c_229,plain,
    ( r1_tarski('#skF_3'('#skF_7'),'#skF_5')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_312,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_41,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_315,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(A_30)
      | A_30 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_45])).

tff(c_18404,plain,(
    ! [B_573] :
      ( '#skF_1'(k1_zfmisc_1(B_573)) = '#skF_7'
      | ~ v1_xboole_0(B_573)
      | v1_xboole_0(k1_zfmisc_1(B_573)) ) ),
    inference(resolution,[status(thm)],[c_18400,c_315])).

tff(c_18840,plain,(
    ! [B_577] :
      ( '#skF_1'(k1_zfmisc_1(B_577)) = '#skF_7'
      | ~ v1_xboole_0(B_577)
      | v1_xboole_0(k1_zfmisc_1(B_577)) ) ),
    inference(resolution,[status(thm)],[c_18400,c_315])).

tff(c_18849,plain,(
    ! [B_578] :
      ( k1_zfmisc_1(B_578) = '#skF_7'
      | '#skF_1'(k1_zfmisc_1(B_578)) = '#skF_7'
      | ~ v1_xboole_0(B_578) ) ),
    inference(resolution,[status(thm)],[c_18840,c_315])).

tff(c_18395,plain,(
    ! [B_571] :
      ( ~ v1_xboole_0(B_571)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(B_571)))
      | v1_xboole_0(k1_zfmisc_1(B_571)) ) ),
    inference(resolution,[status(thm)],[c_86,c_18298])).

tff(c_18855,plain,(
    ! [B_578] :
      ( ~ v1_xboole_0(B_578)
      | v1_xboole_0('#skF_7')
      | v1_xboole_0(k1_zfmisc_1(B_578))
      | k1_zfmisc_1(B_578) = '#skF_7'
      | ~ v1_xboole_0(B_578) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18849,c_18395])).

tff(c_18955,plain,(
    ! [B_579] :
      ( ~ v1_xboole_0(B_579)
      | v1_xboole_0(k1_zfmisc_1(B_579))
      | k1_zfmisc_1(B_579) = '#skF_7'
      | ~ v1_xboole_0(B_579) ) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_18855])).

tff(c_18965,plain,(
    ! [B_580] :
      ( k1_zfmisc_1(B_580) = '#skF_7'
      | ~ v1_xboole_0(B_580) ) ),
    inference(resolution,[status(thm)],[c_18955,c_315])).

tff(c_18974,plain,(
    ! [B_581] :
      ( k1_zfmisc_1(k1_zfmisc_1(B_581)) = '#skF_7'
      | '#skF_1'(k1_zfmisc_1(B_581)) = '#skF_7'
      | ~ v1_xboole_0(B_581) ) ),
    inference(resolution,[status(thm)],[c_18404,c_18965])).

tff(c_265,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_5')
      | ~ r2_hidden(A_64,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_231,c_20])).

tff(c_294,plain,
    ( r1_tarski('#skF_3'('#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_265])).

tff(c_323,plain,
    ( r1_tarski('#skF_3'('#skF_6'),'#skF_5')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_294])).

tff(c_324,plain,(
    r1_tarski('#skF_3'('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_323])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_799,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_hidden(A_102,B_103)
      | ~ r1_tarski(B_104,B_103)
      | v1_xboole_0(B_104)
      | ~ m1_subset_1(A_102,B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_839,plain,(
    ! [A_102] :
      ( r2_hidden(A_102,'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_6'))
      | ~ m1_subset_1(A_102,'#skF_3'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_324,c_799])).

tff(c_1883,plain,(
    v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_1887,plain,(
    '#skF_3'('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1883,c_315])).

tff(c_1888,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1887,c_1883])).

tff(c_1897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_1888])).

tff(c_1899,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_316,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_12])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1140,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(A_118,B_119)
      | ~ r1_tarski('#skF_7',B_119)
      | ~ r2_hidden(A_118,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_243,c_6])).

tff(c_1157,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_3'('#skF_6'),B_119)
      | ~ r1_tarski('#skF_7',B_119)
      | '#skF_7' = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_316,c_1140])).

tff(c_1192,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_3'('#skF_6'),B_120)
      | ~ r1_tarski('#skF_7',B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1157])).

tff(c_150,plain,(
    ! [A_56,B_18,A_17] :
      ( m1_subset_1(A_56,B_18)
      | ~ r2_hidden(A_56,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_2119,plain,(
    ! [B_151,B_152] :
      ( m1_subset_1('#skF_3'('#skF_6'),B_151)
      | ~ r1_tarski(B_152,B_151)
      | ~ r1_tarski('#skF_7',B_152) ) ),
    inference(resolution,[status(thm)],[c_1192,c_150])).

tff(c_2622,plain,(
    ! [A_168] :
      ( m1_subset_1('#skF_3'('#skF_6'),A_168)
      | ~ r1_tarski('#skF_7',A_168) ) ),
    inference(resolution,[status(thm)],[c_86,c_2119])).

tff(c_2998,plain,(
    ! [B_183] :
      ( r1_tarski('#skF_3'('#skF_6'),B_183)
      | ~ r1_tarski('#skF_7',k1_zfmisc_1(B_183)) ) ),
    inference(resolution,[status(thm)],[c_2622,c_20])).

tff(c_3022,plain,(
    ! [B_183] :
      ( ~ v1_xboole_0(B_183)
      | v1_xboole_0('#skF_3'('#skF_6'))
      | ~ r1_tarski('#skF_7',k1_zfmisc_1(B_183)) ) ),
    inference(resolution,[status(thm)],[c_2998,c_142])).

tff(c_3038,plain,(
    ! [B_183] :
      ( ~ v1_xboole_0(B_183)
      | ~ r1_tarski('#skF_7',k1_zfmisc_1(B_183)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1899,c_3022])).

tff(c_19055,plain,(
    ! [B_581] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_581))
      | ~ r1_tarski('#skF_7','#skF_7')
      | '#skF_1'(k1_zfmisc_1(B_581)) = '#skF_7'
      | ~ v1_xboole_0(B_581) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18974,c_3038])).

tff(c_19092,plain,(
    ! [B_582] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_582))
      | '#skF_1'(k1_zfmisc_1(B_582)) = '#skF_7'
      | ~ v1_xboole_0(B_582) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_19055])).

tff(c_19100,plain,(
    ! [B_583] :
      ( '#skF_1'(k1_zfmisc_1(B_583)) = '#skF_7'
      | ~ v1_xboole_0(B_583) ) ),
    inference(resolution,[status(thm)],[c_18404,c_19092])).

tff(c_19106,plain,(
    ! [B_583] :
      ( ~ v1_xboole_0(B_583)
      | v1_xboole_0('#skF_7')
      | v1_xboole_0(k1_zfmisc_1(B_583))
      | ~ v1_xboole_0(B_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19100,c_18395])).

tff(c_19191,plain,(
    ! [B_583] :
      ( ~ v1_xboole_0(B_583)
      | v1_xboole_0(k1_zfmisc_1(B_583))
      | ~ v1_xboole_0(B_583) ) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_19106])).

tff(c_19215,plain,(
    ! [B_585] :
      ( ~ v1_xboole_0(B_585)
      | v1_xboole_0(k1_zfmisc_1(B_585))
      | ~ v1_xboole_0(B_585) ) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_19106])).

tff(c_18962,plain,(
    ! [B_579] :
      ( k1_zfmisc_1(B_579) = '#skF_7'
      | ~ v1_xboole_0(B_579) ) ),
    inference(resolution,[status(thm)],[c_18955,c_315])).

tff(c_19228,plain,(
    ! [B_586] :
      ( k1_zfmisc_1(k1_zfmisc_1(B_586)) = '#skF_7'
      | ~ v1_xboole_0(B_586) ) ),
    inference(resolution,[status(thm)],[c_19215,c_18962])).

tff(c_19315,plain,(
    ! [B_586] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_586))
      | ~ r1_tarski('#skF_7','#skF_7')
      | ~ v1_xboole_0(B_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19228,c_3038])).

tff(c_19355,plain,(
    ! [B_587] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_587))
      | ~ v1_xboole_0(B_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_19315])).

tff(c_19362,plain,(
    ! [B_583] : ~ v1_xboole_0(B_583) ),
    inference(resolution,[status(thm)],[c_19191,c_19355])).

tff(c_19532,plain,(
    ! [A_590,B_591] :
      ( r2_hidden(A_590,B_591)
      | ~ m1_subset_1(A_590,B_591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19362,c_18])).

tff(c_241,plain,(
    ! [A_62] :
      ( r2_hidden(A_62,'#skF_7')
      | ~ r2_hidden(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_231,c_34])).

tff(c_447,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden('#skF_4'(A_75,B_76),B_76)
      | B_76 = A_75
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_456,plain,(
    ! [A_75] :
      ( A_75 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_75))
      | ~ r2_hidden('#skF_4'(A_75,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_241,c_447])).

tff(c_27135,plain,(
    ! [A_754] :
      ( A_754 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_754))
      | ~ m1_subset_1('#skF_4'(A_754,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_19532,c_456])).

tff(c_27139,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_16,c_27135])).

tff(c_27142,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_27139])).

tff(c_27145,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_27142])).

tff(c_27149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_27145])).

tff(c_27151,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_198,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_55311,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_27151,c_198])).

tff(c_55323,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_55311,c_2])).

tff(c_55324,plain,(
    ! [A_1491,B_1492] :
      ( ~ r2_hidden('#skF_4'(A_1491,B_1492),B_1492)
      | B_1492 = A_1491
      | ~ m1_subset_1(B_1492,k1_zfmisc_1(A_1491)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56468,plain,(
    ! [A_1550] :
      ( A_1550 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1550))
      | ~ r2_hidden('#skF_4'(A_1550,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_241,c_55324])).

tff(c_56477,plain,(
    ! [A_1550] :
      ( A_1550 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1550))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_4'(A_1550,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_56468])).

tff(c_80533,plain,(
    ! [A_2220] :
      ( A_2220 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2220))
      | ~ m1_subset_1('#skF_4'(A_2220,'#skF_7'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55323,c_56477])).

tff(c_80537,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_16,c_80533])).

tff(c_80540,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_80537])).

tff(c_80543,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_80540])).

tff(c_80547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55563,c_80543])).

tff(c_80563,plain,(
    ! [A_2221] : ~ r2_hidden(A_2221,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_80583,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_80563])).

tff(c_80549,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_80553,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_80549,c_45])).

tff(c_80621,plain,(
    ! [A_2227] :
      ( ~ v1_xboole_0(A_2227)
      | A_2227 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80553,c_45])).

tff(c_80624,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_80583,c_80621])).

tff(c_80631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_80624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.45/11.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.45/11.46  
% 20.45/11.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.45/11.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 20.45/11.47  
% 20.45/11.47  %Foreground sorts:
% 20.45/11.47  
% 20.45/11.47  
% 20.45/11.47  %Background operators:
% 20.45/11.47  
% 20.45/11.47  
% 20.45/11.47  %Foreground operators:
% 20.45/11.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.45/11.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.45/11.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 20.45/11.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.45/11.47  tff('#skF_7', type, '#skF_7': $i).
% 20.45/11.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.45/11.47  tff('#skF_5', type, '#skF_5': $i).
% 20.45/11.47  tff('#skF_6', type, '#skF_6': $i).
% 20.45/11.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.45/11.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.45/11.47  tff('#skF_3', type, '#skF_3': $i > $i).
% 20.45/11.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.45/11.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.45/11.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.45/11.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.45/11.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.45/11.47  
% 20.55/11.49  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 20.55/11.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 20.55/11.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.55/11.49  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 20.55/11.49  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.55/11.49  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 20.55/11.49  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 20.55/11.49  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 20.55/11.49  tff(c_26, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.55/11.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.55/11.49  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.55/11.49  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.55/11.49  tff(c_143, plain, (![A_56, C_57, B_58]: (m1_subset_1(A_56, C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.55/11.49  tff(c_153, plain, (![A_59]: (m1_subset_1(A_59, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_59, '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_143])).
% 20.55/11.49  tff(c_32, plain, (![D_26]: (r2_hidden(D_26, '#skF_6') | ~r2_hidden(D_26, '#skF_7') | ~m1_subset_1(D_26, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.55/11.49  tff(c_169, plain, (![A_60]: (r2_hidden(A_60, '#skF_6') | ~r2_hidden(A_60, '#skF_7'))), inference(resolution, [status(thm)], [c_153, c_32])).
% 20.55/11.49  tff(c_55542, plain, (![B_1503]: (r2_hidden('#skF_2'('#skF_7', B_1503), '#skF_6') | r1_tarski('#skF_7', B_1503))), inference(resolution, [status(thm)], [c_10, c_169])).
% 20.55/11.49  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.55/11.49  tff(c_55563, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_55542, c_8])).
% 20.55/11.49  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.55/11.49  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1('#skF_4'(A_12, B_13), A_12) | B_13=A_12 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.55/11.49  tff(c_523, plain, (![B_80]: (r2_hidden('#skF_2'('#skF_7', B_80), '#skF_6') | r1_tarski('#skF_7', B_80))), inference(resolution, [status(thm)], [c_10, c_169])).
% 20.55/11.49  tff(c_538, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_523, c_8])).
% 20.55/11.49  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.55/11.49  tff(c_231, plain, (![A_62]: (m1_subset_1(A_62, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_143])).
% 20.55/11.49  tff(c_34, plain, (![D_26]: (r2_hidden(D_26, '#skF_7') | ~r2_hidden(D_26, '#skF_6') | ~m1_subset_1(D_26, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 20.55/11.49  tff(c_243, plain, (![A_63]: (r2_hidden(A_63, '#skF_7') | ~r2_hidden(A_63, '#skF_6'))), inference(resolution, [status(thm)], [c_231, c_34])).
% 20.55/11.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.55/11.49  tff(c_263, plain, (![A_63]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_63, '#skF_6'))), inference(resolution, [status(thm)], [c_243, c_2])).
% 20.55/11.49  tff(c_264, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_263])).
% 20.55/11.49  tff(c_78, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.55/11.49  tff(c_86, plain, (![A_41]: (r1_tarski(A_41, A_41))), inference(resolution, [status(thm)], [c_78, c_8])).
% 20.55/11.49  tff(c_595, plain, (![A_84, B_85, A_86]: (m1_subset_1(A_84, B_85) | ~r2_hidden(A_84, A_86) | ~r1_tarski(A_86, B_85))), inference(resolution, [status(thm)], [c_22, c_143])).
% 20.55/11.49  tff(c_789, plain, (![A_100, B_101]: (m1_subset_1('#skF_1'(A_100), B_101) | ~r1_tarski(A_100, B_101) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_4, c_595])).
% 20.55/11.49  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.55/11.49  tff(c_5328, plain, (![A_270, B_271]: (r1_tarski('#skF_1'(A_270), B_271) | ~r1_tarski(A_270, k1_zfmisc_1(B_271)) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_789, c_20])).
% 20.55/11.49  tff(c_88, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.55/11.49  tff(c_135, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54), B_55) | ~r1_tarski(A_54, B_55) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_4, c_88])).
% 20.55/11.49  tff(c_142, plain, (![B_55, A_54]: (~v1_xboole_0(B_55) | ~r1_tarski(A_54, B_55) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_135, c_2])).
% 20.55/11.49  tff(c_18298, plain, (![B_571, A_572]: (~v1_xboole_0(B_571) | v1_xboole_0('#skF_1'(A_572)) | ~r1_tarski(A_572, k1_zfmisc_1(B_571)) | v1_xboole_0(A_572))), inference(resolution, [status(thm)], [c_5328, c_142])).
% 20.55/11.49  tff(c_18400, plain, (![B_573]: (~v1_xboole_0(B_573) | v1_xboole_0('#skF_1'(k1_zfmisc_1(B_573))) | v1_xboole_0(k1_zfmisc_1(B_573)))), inference(resolution, [status(thm)], [c_86, c_18298])).
% 20.55/11.49  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.55/11.49  tff(c_200, plain, (![A_61]: (r1_tarski(A_61, '#skF_5') | ~r2_hidden(A_61, '#skF_7'))), inference(resolution, [status(thm)], [c_153, c_20])).
% 20.55/11.49  tff(c_229, plain, (r1_tarski('#skF_3'('#skF_7'), '#skF_5') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_12, c_200])).
% 20.55/11.49  tff(c_312, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_229])).
% 20.55/11.49  tff(c_41, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.55/11.49  tff(c_45, plain, (![A_30]: (~v1_xboole_0(A_30) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_41, c_2])).
% 20.55/11.49  tff(c_315, plain, (![A_30]: (~v1_xboole_0(A_30) | A_30='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_45])).
% 20.55/11.49  tff(c_18404, plain, (![B_573]: ('#skF_1'(k1_zfmisc_1(B_573))='#skF_7' | ~v1_xboole_0(B_573) | v1_xboole_0(k1_zfmisc_1(B_573)))), inference(resolution, [status(thm)], [c_18400, c_315])).
% 20.55/11.49  tff(c_18840, plain, (![B_577]: ('#skF_1'(k1_zfmisc_1(B_577))='#skF_7' | ~v1_xboole_0(B_577) | v1_xboole_0(k1_zfmisc_1(B_577)))), inference(resolution, [status(thm)], [c_18400, c_315])).
% 20.55/11.49  tff(c_18849, plain, (![B_578]: (k1_zfmisc_1(B_578)='#skF_7' | '#skF_1'(k1_zfmisc_1(B_578))='#skF_7' | ~v1_xboole_0(B_578))), inference(resolution, [status(thm)], [c_18840, c_315])).
% 20.55/11.49  tff(c_18395, plain, (![B_571]: (~v1_xboole_0(B_571) | v1_xboole_0('#skF_1'(k1_zfmisc_1(B_571))) | v1_xboole_0(k1_zfmisc_1(B_571)))), inference(resolution, [status(thm)], [c_86, c_18298])).
% 20.55/11.49  tff(c_18855, plain, (![B_578]: (~v1_xboole_0(B_578) | v1_xboole_0('#skF_7') | v1_xboole_0(k1_zfmisc_1(B_578)) | k1_zfmisc_1(B_578)='#skF_7' | ~v1_xboole_0(B_578))), inference(superposition, [status(thm), theory('equality')], [c_18849, c_18395])).
% 20.55/11.49  tff(c_18955, plain, (![B_579]: (~v1_xboole_0(B_579) | v1_xboole_0(k1_zfmisc_1(B_579)) | k1_zfmisc_1(B_579)='#skF_7' | ~v1_xboole_0(B_579))), inference(negUnitSimplification, [status(thm)], [c_264, c_18855])).
% 20.55/11.49  tff(c_18965, plain, (![B_580]: (k1_zfmisc_1(B_580)='#skF_7' | ~v1_xboole_0(B_580))), inference(resolution, [status(thm)], [c_18955, c_315])).
% 20.55/11.49  tff(c_18974, plain, (![B_581]: (k1_zfmisc_1(k1_zfmisc_1(B_581))='#skF_7' | '#skF_1'(k1_zfmisc_1(B_581))='#skF_7' | ~v1_xboole_0(B_581))), inference(resolution, [status(thm)], [c_18404, c_18965])).
% 20.55/11.49  tff(c_265, plain, (![A_64]: (r1_tarski(A_64, '#skF_5') | ~r2_hidden(A_64, '#skF_6'))), inference(resolution, [status(thm)], [c_231, c_20])).
% 20.55/11.49  tff(c_294, plain, (r1_tarski('#skF_3'('#skF_6'), '#skF_5') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_12, c_265])).
% 20.55/11.49  tff(c_323, plain, (r1_tarski('#skF_3'('#skF_6'), '#skF_5') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_294])).
% 20.55/11.49  tff(c_324, plain, (r1_tarski('#skF_3'('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_26, c_323])).
% 20.55/11.49  tff(c_18, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 20.55/11.49  tff(c_799, plain, (![A_102, B_103, B_104]: (r2_hidden(A_102, B_103) | ~r1_tarski(B_104, B_103) | v1_xboole_0(B_104) | ~m1_subset_1(A_102, B_104))), inference(resolution, [status(thm)], [c_18, c_88])).
% 20.55/11.49  tff(c_839, plain, (![A_102]: (r2_hidden(A_102, '#skF_5') | v1_xboole_0('#skF_3'('#skF_6')) | ~m1_subset_1(A_102, '#skF_3'('#skF_6')))), inference(resolution, [status(thm)], [c_324, c_799])).
% 20.55/11.49  tff(c_1883, plain, (v1_xboole_0('#skF_3'('#skF_6'))), inference(splitLeft, [status(thm)], [c_839])).
% 20.55/11.49  tff(c_1887, plain, ('#skF_3'('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_1883, c_315])).
% 20.55/11.49  tff(c_1888, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1887, c_1883])).
% 20.55/11.49  tff(c_1897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_1888])).
% 20.55/11.49  tff(c_1899, plain, (~v1_xboole_0('#skF_3'('#skF_6'))), inference(splitRight, [status(thm)], [c_839])).
% 20.55/11.49  tff(c_316, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_12])).
% 20.55/11.49  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.55/11.49  tff(c_1140, plain, (![A_118, B_119]: (r2_hidden(A_118, B_119) | ~r1_tarski('#skF_7', B_119) | ~r2_hidden(A_118, '#skF_6'))), inference(resolution, [status(thm)], [c_243, c_6])).
% 20.55/11.49  tff(c_1157, plain, (![B_119]: (r2_hidden('#skF_3'('#skF_6'), B_119) | ~r1_tarski('#skF_7', B_119) | '#skF_7'='#skF_6')), inference(resolution, [status(thm)], [c_316, c_1140])).
% 20.55/11.49  tff(c_1192, plain, (![B_120]: (r2_hidden('#skF_3'('#skF_6'), B_120) | ~r1_tarski('#skF_7', B_120))), inference(negUnitSimplification, [status(thm)], [c_26, c_1157])).
% 20.55/11.49  tff(c_150, plain, (![A_56, B_18, A_17]: (m1_subset_1(A_56, B_18) | ~r2_hidden(A_56, A_17) | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_22, c_143])).
% 20.55/11.49  tff(c_2119, plain, (![B_151, B_152]: (m1_subset_1('#skF_3'('#skF_6'), B_151) | ~r1_tarski(B_152, B_151) | ~r1_tarski('#skF_7', B_152))), inference(resolution, [status(thm)], [c_1192, c_150])).
% 20.55/11.49  tff(c_2622, plain, (![A_168]: (m1_subset_1('#skF_3'('#skF_6'), A_168) | ~r1_tarski('#skF_7', A_168))), inference(resolution, [status(thm)], [c_86, c_2119])).
% 20.55/11.49  tff(c_2998, plain, (![B_183]: (r1_tarski('#skF_3'('#skF_6'), B_183) | ~r1_tarski('#skF_7', k1_zfmisc_1(B_183)))), inference(resolution, [status(thm)], [c_2622, c_20])).
% 20.55/11.49  tff(c_3022, plain, (![B_183]: (~v1_xboole_0(B_183) | v1_xboole_0('#skF_3'('#skF_6')) | ~r1_tarski('#skF_7', k1_zfmisc_1(B_183)))), inference(resolution, [status(thm)], [c_2998, c_142])).
% 20.55/11.49  tff(c_3038, plain, (![B_183]: (~v1_xboole_0(B_183) | ~r1_tarski('#skF_7', k1_zfmisc_1(B_183)))), inference(negUnitSimplification, [status(thm)], [c_1899, c_3022])).
% 20.55/11.49  tff(c_19055, plain, (![B_581]: (~v1_xboole_0(k1_zfmisc_1(B_581)) | ~r1_tarski('#skF_7', '#skF_7') | '#skF_1'(k1_zfmisc_1(B_581))='#skF_7' | ~v1_xboole_0(B_581))), inference(superposition, [status(thm), theory('equality')], [c_18974, c_3038])).
% 20.55/11.49  tff(c_19092, plain, (![B_582]: (~v1_xboole_0(k1_zfmisc_1(B_582)) | '#skF_1'(k1_zfmisc_1(B_582))='#skF_7' | ~v1_xboole_0(B_582))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_19055])).
% 20.55/11.49  tff(c_19100, plain, (![B_583]: ('#skF_1'(k1_zfmisc_1(B_583))='#skF_7' | ~v1_xboole_0(B_583))), inference(resolution, [status(thm)], [c_18404, c_19092])).
% 20.55/11.49  tff(c_19106, plain, (![B_583]: (~v1_xboole_0(B_583) | v1_xboole_0('#skF_7') | v1_xboole_0(k1_zfmisc_1(B_583)) | ~v1_xboole_0(B_583))), inference(superposition, [status(thm), theory('equality')], [c_19100, c_18395])).
% 20.55/11.49  tff(c_19191, plain, (![B_583]: (~v1_xboole_0(B_583) | v1_xboole_0(k1_zfmisc_1(B_583)) | ~v1_xboole_0(B_583))), inference(negUnitSimplification, [status(thm)], [c_264, c_19106])).
% 20.55/11.49  tff(c_19215, plain, (![B_585]: (~v1_xboole_0(B_585) | v1_xboole_0(k1_zfmisc_1(B_585)) | ~v1_xboole_0(B_585))), inference(negUnitSimplification, [status(thm)], [c_264, c_19106])).
% 20.55/11.49  tff(c_18962, plain, (![B_579]: (k1_zfmisc_1(B_579)='#skF_7' | ~v1_xboole_0(B_579))), inference(resolution, [status(thm)], [c_18955, c_315])).
% 20.55/11.49  tff(c_19228, plain, (![B_586]: (k1_zfmisc_1(k1_zfmisc_1(B_586))='#skF_7' | ~v1_xboole_0(B_586))), inference(resolution, [status(thm)], [c_19215, c_18962])).
% 20.55/11.49  tff(c_19315, plain, (![B_586]: (~v1_xboole_0(k1_zfmisc_1(B_586)) | ~r1_tarski('#skF_7', '#skF_7') | ~v1_xboole_0(B_586))), inference(superposition, [status(thm), theory('equality')], [c_19228, c_3038])).
% 20.55/11.49  tff(c_19355, plain, (![B_587]: (~v1_xboole_0(k1_zfmisc_1(B_587)) | ~v1_xboole_0(B_587))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_19315])).
% 20.55/11.49  tff(c_19362, plain, (![B_583]: (~v1_xboole_0(B_583))), inference(resolution, [status(thm)], [c_19191, c_19355])).
% 20.55/11.49  tff(c_19532, plain, (![A_590, B_591]: (r2_hidden(A_590, B_591) | ~m1_subset_1(A_590, B_591))), inference(negUnitSimplification, [status(thm)], [c_19362, c_18])).
% 20.55/11.49  tff(c_241, plain, (![A_62]: (r2_hidden(A_62, '#skF_7') | ~r2_hidden(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_231, c_34])).
% 20.55/11.49  tff(c_447, plain, (![A_75, B_76]: (~r2_hidden('#skF_4'(A_75, B_76), B_76) | B_76=A_75 | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.55/11.49  tff(c_456, plain, (![A_75]: (A_75='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_75)) | ~r2_hidden('#skF_4'(A_75, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_241, c_447])).
% 20.55/11.49  tff(c_27135, plain, (![A_754]: (A_754='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_754)) | ~m1_subset_1('#skF_4'(A_754, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_19532, c_456])).
% 20.55/11.49  tff(c_27139, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_27135])).
% 20.55/11.49  tff(c_27142, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_27139])).
% 20.55/11.49  tff(c_27145, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_27142])).
% 20.55/11.49  tff(c_27149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_538, c_27145])).
% 20.55/11.49  tff(c_27151, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_229])).
% 20.55/11.49  tff(c_198, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_12, c_169])).
% 20.55/11.49  tff(c_55311, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_27151, c_198])).
% 20.55/11.49  tff(c_55323, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_55311, c_2])).
% 20.55/11.49  tff(c_55324, plain, (![A_1491, B_1492]: (~r2_hidden('#skF_4'(A_1491, B_1492), B_1492) | B_1492=A_1491 | ~m1_subset_1(B_1492, k1_zfmisc_1(A_1491)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.55/11.49  tff(c_56468, plain, (![A_1550]: (A_1550='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1550)) | ~r2_hidden('#skF_4'(A_1550, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_241, c_55324])).
% 20.55/11.49  tff(c_56477, plain, (![A_1550]: (A_1550='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1550)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_4'(A_1550, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_18, c_56468])).
% 20.55/11.49  tff(c_80533, plain, (![A_2220]: (A_2220='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2220)) | ~m1_subset_1('#skF_4'(A_2220, '#skF_7'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_55323, c_56477])).
% 20.55/11.49  tff(c_80537, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_80533])).
% 20.55/11.49  tff(c_80540, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_80537])).
% 20.55/11.49  tff(c_80543, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_80540])).
% 20.55/11.49  tff(c_80547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55563, c_80543])).
% 20.55/11.49  tff(c_80563, plain, (![A_2221]: (~r2_hidden(A_2221, '#skF_6'))), inference(splitRight, [status(thm)], [c_263])).
% 20.55/11.49  tff(c_80583, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_80563])).
% 20.55/11.49  tff(c_80549, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_263])).
% 20.55/11.49  tff(c_80553, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_80549, c_45])).
% 20.55/11.49  tff(c_80621, plain, (![A_2227]: (~v1_xboole_0(A_2227) | A_2227='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80553, c_45])).
% 20.55/11.49  tff(c_80624, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_80583, c_80621])).
% 20.55/11.49  tff(c_80631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_80624])).
% 20.55/11.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.55/11.49  
% 20.55/11.49  Inference rules
% 20.55/11.49  ----------------------
% 20.55/11.49  #Ref     : 0
% 20.55/11.49  #Sup     : 18254
% 20.55/11.49  #Fact    : 0
% 20.55/11.49  #Define  : 0
% 20.55/11.49  #Split   : 177
% 20.55/11.49  #Chain   : 0
% 20.55/11.49  #Close   : 0
% 20.55/11.49  
% 20.55/11.49  Ordering : KBO
% 20.55/11.49  
% 20.55/11.49  Simplification rules
% 20.55/11.49  ----------------------
% 20.55/11.49  #Subsume      : 9304
% 20.55/11.49  #Demod        : 6914
% 20.55/11.49  #Tautology    : 2338
% 20.55/11.49  #SimpNegUnit  : 1846
% 20.55/11.49  #BackRed      : 1045
% 20.55/11.49  
% 20.55/11.49  #Partial instantiations: 0
% 20.55/11.49  #Strategies tried      : 1
% 20.55/11.49  
% 20.55/11.49  Timing (in seconds)
% 20.55/11.49  ----------------------
% 20.55/11.49  Preprocessing        : 0.29
% 20.55/11.49  Parsing              : 0.15
% 20.55/11.49  CNF conversion       : 0.02
% 20.55/11.49  Main loop            : 10.42
% 20.55/11.49  Inferencing          : 2.02
% 20.55/11.49  Reduction            : 3.06
% 20.55/11.49  Demodulation         : 1.83
% 20.55/11.49  BG Simplification    : 0.17
% 20.55/11.49  Subsumption          : 4.26
% 20.55/11.49  Abstraction          : 0.26
% 20.55/11.49  MUC search           : 0.00
% 20.55/11.49  Cooper               : 0.00
% 20.55/11.49  Total                : 10.75
% 20.55/11.49  Index Insertion      : 0.00
% 20.55/11.49  Index Deletion       : 0.00
% 20.55/11.49  Index Matching       : 0.00
% 20.55/11.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
