%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 155 expanded)
%              Number of leaves         :   46 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 267 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_119,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_148,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [A_81,B_82] : r1_tarski(k3_xboole_0(A_81,B_82),A_81) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_117,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_114])).

tff(c_173,plain,(
    ! [B_100,C_101,A_102] :
      ( r2_hidden(B_100,C_101)
      | ~ r1_tarski(k2_tarski(A_102,B_100),C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_178,plain,(
    ! [B_100,A_102] : r2_hidden(B_100,k2_tarski(A_102,B_100)) ),
    inference(resolution,[status(thm)],[c_117,c_173])).

tff(c_84,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k2_tarski(A_41,B_42),C_43)
      | ~ r2_hidden(B_42,C_43)
      | ~ r2_hidden(A_41,C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_211,plain,(
    ! [A_115,C_116,B_117] :
      ( r2_hidden(A_115,C_116)
      | ~ r1_tarski(k2_tarski(A_115,B_117),C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_216,plain,(
    ! [A_115,B_117] : r2_hidden(A_115,k2_tarski(A_115,B_117)) ),
    inference(resolution,[status(thm)],[c_117,c_211])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_159,plain,(
    ! [A_98,B_99] :
      ( k3_xboole_0(A_98,B_99) = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_422,plain,(
    ! [A_179,B_180] : k3_xboole_0(k4_xboole_0(A_179,B_180),A_179) = k4_xboole_0(A_179,B_180) ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r1_xboole_0(A_130,B_131)
      | ~ r2_hidden(C_132,k3_xboole_0(A_130,B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_238,plain,(
    ! [A_135,B_136] :
      ( ~ r1_xboole_0(A_135,B_136)
      | v1_xboole_0(k3_xboole_0(A_135,B_136)) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [B_86,A_87] :
      ( ~ v1_xboole_0(B_86)
      | B_86 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_123,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_250,plain,(
    ! [A_138,B_139] :
      ( k3_xboole_0(A_138,B_139) = k1_xboole_0
      | ~ r1_xboole_0(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_238,c_123])).

tff(c_254,plain,(
    ! [A_23,B_24] : k3_xboole_0(k4_xboole_0(A_23,B_24),B_24) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_250])).

tff(c_435,plain,(
    ! [A_179] : k4_xboole_0(A_179,A_179) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_254])).

tff(c_835,plain,(
    ! [A_210,C_211,B_212] :
      ( ~ r2_hidden(A_210,C_211)
      | k4_xboole_0(k2_tarski(A_210,B_212),C_211) != k2_tarski(A_210,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_839,plain,(
    ! [A_210,B_212] :
      ( ~ r2_hidden(A_210,k2_tarski(A_210,B_212))
      | k2_tarski(A_210,B_212) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_835])).

tff(c_841,plain,(
    ! [A_210,B_212] : k2_tarski(A_210,B_212) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_839])).

tff(c_650,plain,(
    ! [B_192,A_193] :
      ( r1_tarski(k1_setfam_1(B_192),k1_setfam_1(A_193))
      | k1_xboole_0 = A_193
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_662,plain,(
    ! [B_192,A_56,B_57] :
      ( r1_tarski(k1_setfam_1(B_192),k3_xboole_0(A_56,B_57))
      | k2_tarski(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(k2_tarski(A_56,B_57),B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_650])).

tff(c_19190,plain,(
    ! [B_52238,A_52239,B_52240] :
      ( r1_tarski(k1_setfam_1(B_52238),k3_xboole_0(A_52239,B_52240))
      | ~ r1_tarski(k2_tarski(A_52239,B_52240),B_52238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_662])).

tff(c_19252,plain,(
    ! [B_52466,A_52467] :
      ( r1_tarski(k1_setfam_1(B_52466),A_52467)
      | ~ r1_tarski(k2_tarski(A_52467,A_52467),B_52466) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_19190])).

tff(c_19271,plain,(
    ! [C_52693,B_52694] :
      ( r1_tarski(k1_setfam_1(C_52693),B_52694)
      | ~ r2_hidden(B_52694,C_52693) ) ),
    inference(resolution,[status(thm)],[c_36,c_19252])).

tff(c_19941,plain,(
    ! [A_57470,B_57471,B_57472] :
      ( r1_tarski(k3_xboole_0(A_57470,B_57471),B_57472)
      | ~ r2_hidden(B_57472,k2_tarski(A_57470,B_57471)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_19271])).

tff(c_19969,plain,(
    ! [A_102,B_100] : r1_tarski(k3_xboole_0(A_102,B_100),B_100) ),
    inference(resolution,[status(thm)],[c_178,c_19941])).

tff(c_100,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(A_58,k1_zfmisc_1(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_317,plain,(
    ! [B_152,A_153] :
      ( v1_relat_1(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_322,plain,(
    ! [A_154,B_155] :
      ( v1_relat_1(A_154)
      | ~ v1_relat_1(B_155)
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_88,c_317])).

tff(c_338,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_322])).

tff(c_98,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_102,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2603,plain,(
    ! [C_382,A_383,B_384] :
      ( r1_tarski(k5_relat_1(C_382,A_383),k5_relat_1(C_382,B_384))
      | ~ r1_tarski(A_383,B_384)
      | ~ v1_relat_1(C_382)
      | ~ v1_relat_1(B_384)
      | ~ v1_relat_1(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1514,plain,(
    ! [C_292,A_293,B_294] :
      ( r1_tarski(k5_relat_1(C_292,A_293),k5_relat_1(C_292,B_294))
      | ~ r1_tarski(A_293,B_294)
      | ~ v1_relat_1(C_292)
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_718,plain,(
    ! [A_198,B_199,C_200] :
      ( r1_tarski(A_198,k3_xboole_0(B_199,C_200))
      | ~ r1_tarski(A_198,C_200)
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_96,plain,(
    ~ r1_tarski(k5_relat_1('#skF_5',k3_xboole_0('#skF_6','#skF_7')),k3_xboole_0(k5_relat_1('#skF_5','#skF_6'),k5_relat_1('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_755,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_5',k3_xboole_0('#skF_6','#skF_7')),k5_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski(k5_relat_1('#skF_5',k3_xboole_0('#skF_6','#skF_7')),k5_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_718,c_96])).

tff(c_921,plain,(
    ~ r1_tarski(k5_relat_1('#skF_5',k3_xboole_0('#skF_6','#skF_7')),k5_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_1517,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_6')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1514,c_921])).

tff(c_1526,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_102,c_16,c_1517])).

tff(c_1531,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_338,c_1526])).

tff(c_1535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1531])).

tff(c_1536,plain,(
    ~ r1_tarski(k5_relat_1('#skF_5',k3_xboole_0('#skF_6','#skF_7')),k5_relat_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_2606,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_7')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2603,c_1536])).

tff(c_2615,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_7')
    | ~ v1_relat_1(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_102,c_2606])).

tff(c_2618,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2615])).

tff(c_2621,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_338,c_2618])).

tff(c_2625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2621])).

tff(c_2626,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2615])).

tff(c_20038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19969,c_2626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.54/4.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.44  
% 11.54/4.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.54/4.45  
% 11.54/4.45  %Foreground sorts:
% 11.54/4.45  
% 11.54/4.45  
% 11.54/4.45  %Background operators:
% 11.54/4.45  
% 11.54/4.45  
% 11.54/4.45  %Foreground operators:
% 11.54/4.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.54/4.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.54/4.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.54/4.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.54/4.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.54/4.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.54/4.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.54/4.45  tff('#skF_7', type, '#skF_7': $i).
% 11.54/4.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.54/4.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.54/4.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.54/4.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.54/4.45  tff('#skF_5', type, '#skF_5': $i).
% 11.54/4.45  tff('#skF_6', type, '#skF_6': $i).
% 11.54/4.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.54/4.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.54/4.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.54/4.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.54/4.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 11.54/4.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.54/4.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.54/4.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.54/4.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.54/4.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.54/4.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.54/4.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 11.54/4.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.54/4.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.54/4.45  
% 11.54/4.46  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.54/4.46  tff(f_52, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.54/4.46  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.54/4.46  tff(f_119, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.54/4.46  tff(f_64, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.54/4.46  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.54/4.46  tff(f_66, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.54/4.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.54/4.46  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.54/4.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.54/4.46  tff(f_74, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 11.54/4.46  tff(f_96, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 11.54/4.46  tff(f_129, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 11.54/4.46  tff(f_159, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 11.54/4.46  tff(f_123, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.54/4.46  tff(f_136, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.54/4.46  tff(f_148, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 11.54/4.46  tff(f_58, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 11.54/4.46  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.54/4.46  tff(c_114, plain, (![A_81, B_82]: (r1_tarski(k3_xboole_0(A_81, B_82), A_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.54/4.46  tff(c_117, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_114])).
% 11.54/4.46  tff(c_173, plain, (![B_100, C_101, A_102]: (r2_hidden(B_100, C_101) | ~r1_tarski(k2_tarski(A_102, B_100), C_101))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.54/4.46  tff(c_178, plain, (![B_100, A_102]: (r2_hidden(B_100, k2_tarski(A_102, B_100)))), inference(resolution, [status(thm)], [c_117, c_173])).
% 11.54/4.46  tff(c_84, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.54/4.46  tff(c_36, plain, (![A_41, B_42, C_43]: (r1_tarski(k2_tarski(A_41, B_42), C_43) | ~r2_hidden(B_42, C_43) | ~r2_hidden(A_41, C_43))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.54/4.46  tff(c_211, plain, (![A_115, C_116, B_117]: (r2_hidden(A_115, C_116) | ~r1_tarski(k2_tarski(A_115, B_117), C_116))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.54/4.46  tff(c_216, plain, (![A_115, B_117]: (r2_hidden(A_115, k2_tarski(A_115, B_117)))), inference(resolution, [status(thm)], [c_117, c_211])).
% 11.54/4.46  tff(c_22, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.54/4.46  tff(c_159, plain, (![A_98, B_99]: (k3_xboole_0(A_98, B_99)=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.54/4.46  tff(c_422, plain, (![A_179, B_180]: (k3_xboole_0(k4_xboole_0(A_179, B_180), A_179)=k4_xboole_0(A_179, B_180))), inference(resolution, [status(thm)], [c_22, c_159])).
% 11.54/4.46  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.54/4.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.54/4.46  tff(c_228, plain, (![A_130, B_131, C_132]: (~r1_xboole_0(A_130, B_131) | ~r2_hidden(C_132, k3_xboole_0(A_130, B_131)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.54/4.46  tff(c_238, plain, (![A_135, B_136]: (~r1_xboole_0(A_135, B_136) | v1_xboole_0(k3_xboole_0(A_135, B_136)))), inference(resolution, [status(thm)], [c_4, c_228])).
% 11.54/4.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.54/4.46  tff(c_120, plain, (![B_86, A_87]: (~v1_xboole_0(B_86) | B_86=A_87 | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.54/4.46  tff(c_123, plain, (![A_87]: (k1_xboole_0=A_87 | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_6, c_120])).
% 11.54/4.46  tff(c_250, plain, (![A_138, B_139]: (k3_xboole_0(A_138, B_139)=k1_xboole_0 | ~r1_xboole_0(A_138, B_139))), inference(resolution, [status(thm)], [c_238, c_123])).
% 11.54/4.46  tff(c_254, plain, (![A_23, B_24]: (k3_xboole_0(k4_xboole_0(A_23, B_24), B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_250])).
% 11.54/4.46  tff(c_435, plain, (![A_179]: (k4_xboole_0(A_179, A_179)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_422, c_254])).
% 11.54/4.46  tff(c_835, plain, (![A_210, C_211, B_212]: (~r2_hidden(A_210, C_211) | k4_xboole_0(k2_tarski(A_210, B_212), C_211)!=k2_tarski(A_210, B_212))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.54/4.46  tff(c_839, plain, (![A_210, B_212]: (~r2_hidden(A_210, k2_tarski(A_210, B_212)) | k2_tarski(A_210, B_212)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_435, c_835])).
% 11.54/4.46  tff(c_841, plain, (![A_210, B_212]: (k2_tarski(A_210, B_212)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_216, c_839])).
% 11.54/4.46  tff(c_650, plain, (![B_192, A_193]: (r1_tarski(k1_setfam_1(B_192), k1_setfam_1(A_193)) | k1_xboole_0=A_193 | ~r1_tarski(A_193, B_192))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.54/4.46  tff(c_662, plain, (![B_192, A_56, B_57]: (r1_tarski(k1_setfam_1(B_192), k3_xboole_0(A_56, B_57)) | k2_tarski(A_56, B_57)=k1_xboole_0 | ~r1_tarski(k2_tarski(A_56, B_57), B_192))), inference(superposition, [status(thm), theory('equality')], [c_84, c_650])).
% 11.54/4.46  tff(c_19190, plain, (![B_52238, A_52239, B_52240]: (r1_tarski(k1_setfam_1(B_52238), k3_xboole_0(A_52239, B_52240)) | ~r1_tarski(k2_tarski(A_52239, B_52240), B_52238))), inference(negUnitSimplification, [status(thm)], [c_841, c_662])).
% 11.54/4.46  tff(c_19252, plain, (![B_52466, A_52467]: (r1_tarski(k1_setfam_1(B_52466), A_52467) | ~r1_tarski(k2_tarski(A_52467, A_52467), B_52466))), inference(superposition, [status(thm), theory('equality')], [c_8, c_19190])).
% 11.54/4.46  tff(c_19271, plain, (![C_52693, B_52694]: (r1_tarski(k1_setfam_1(C_52693), B_52694) | ~r2_hidden(B_52694, C_52693))), inference(resolution, [status(thm)], [c_36, c_19252])).
% 11.54/4.46  tff(c_19941, plain, (![A_57470, B_57471, B_57472]: (r1_tarski(k3_xboole_0(A_57470, B_57471), B_57472) | ~r2_hidden(B_57472, k2_tarski(A_57470, B_57471)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_19271])).
% 11.54/4.46  tff(c_19969, plain, (![A_102, B_100]: (r1_tarski(k3_xboole_0(A_102, B_100), B_100))), inference(resolution, [status(thm)], [c_178, c_19941])).
% 11.54/4.46  tff(c_100, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 11.54/4.46  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.54/4.46  tff(c_88, plain, (![A_58, B_59]: (m1_subset_1(A_58, k1_zfmisc_1(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.54/4.46  tff(c_317, plain, (![B_152, A_153]: (v1_relat_1(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.54/4.46  tff(c_322, plain, (![A_154, B_155]: (v1_relat_1(A_154) | ~v1_relat_1(B_155) | ~r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_88, c_317])).
% 11.54/4.46  tff(c_338, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_16, c_322])).
% 11.54/4.46  tff(c_98, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 11.54/4.46  tff(c_102, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 11.54/4.46  tff(c_2603, plain, (![C_382, A_383, B_384]: (r1_tarski(k5_relat_1(C_382, A_383), k5_relat_1(C_382, B_384)) | ~r1_tarski(A_383, B_384) | ~v1_relat_1(C_382) | ~v1_relat_1(B_384) | ~v1_relat_1(A_383))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.54/4.46  tff(c_1514, plain, (![C_292, A_293, B_294]: (r1_tarski(k5_relat_1(C_292, A_293), k5_relat_1(C_292, B_294)) | ~r1_tarski(A_293, B_294) | ~v1_relat_1(C_292) | ~v1_relat_1(B_294) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.54/4.46  tff(c_718, plain, (![A_198, B_199, C_200]: (r1_tarski(A_198, k3_xboole_0(B_199, C_200)) | ~r1_tarski(A_198, C_200) | ~r1_tarski(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.54/4.46  tff(c_96, plain, (~r1_tarski(k5_relat_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')), k3_xboole_0(k5_relat_1('#skF_5', '#skF_6'), k5_relat_1('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 11.54/4.46  tff(c_755, plain, (~r1_tarski(k5_relat_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')), k5_relat_1('#skF_5', '#skF_7')) | ~r1_tarski(k5_relat_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')), k5_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_718, c_96])).
% 11.54/4.46  tff(c_921, plain, (~r1_tarski(k5_relat_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')), k5_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_755])).
% 11.54/4.46  tff(c_1517, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_6') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k3_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1514, c_921])).
% 11.54/4.46  tff(c_1526, plain, (~v1_relat_1(k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_102, c_16, c_1517])).
% 11.54/4.46  tff(c_1531, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_338, c_1526])).
% 11.54/4.46  tff(c_1535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_1531])).
% 11.54/4.46  tff(c_1536, plain, (~r1_tarski(k5_relat_1('#skF_5', k3_xboole_0('#skF_6', '#skF_7')), k5_relat_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_755])).
% 11.54/4.46  tff(c_2606, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_7') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_7') | ~v1_relat_1(k3_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2603, c_1536])).
% 11.54/4.46  tff(c_2615, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_7') | ~v1_relat_1(k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_102, c_2606])).
% 11.54/4.46  tff(c_2618, plain, (~v1_relat_1(k3_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_2615])).
% 11.54/4.46  tff(c_2621, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_338, c_2618])).
% 11.54/4.46  tff(c_2625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_2621])).
% 11.54/4.46  tff(c_2626, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_2615])).
% 11.54/4.46  tff(c_20038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19969, c_2626])).
% 11.54/4.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.46  
% 11.54/4.46  Inference rules
% 11.54/4.46  ----------------------
% 11.54/4.46  #Ref     : 0
% 11.54/4.46  #Sup     : 3731
% 11.54/4.46  #Fact    : 100
% 11.54/4.46  #Define  : 0
% 11.54/4.46  #Split   : 9
% 11.54/4.46  #Chain   : 0
% 11.54/4.46  #Close   : 0
% 11.54/4.46  
% 11.54/4.46  Ordering : KBO
% 11.54/4.46  
% 11.54/4.46  Simplification rules
% 11.54/4.46  ----------------------
% 11.54/4.46  #Subsume      : 1099
% 11.54/4.46  #Demod        : 2266
% 11.54/4.46  #Tautology    : 1413
% 11.54/4.46  #SimpNegUnit  : 92
% 11.54/4.46  #BackRed      : 6
% 11.54/4.46  
% 11.54/4.46  #Partial instantiations: 24111
% 11.54/4.46  #Strategies tried      : 1
% 11.54/4.46  
% 11.54/4.46  Timing (in seconds)
% 11.54/4.46  ----------------------
% 11.54/4.46  Preprocessing        : 0.40
% 11.54/4.46  Parsing              : 0.20
% 11.54/4.47  CNF conversion       : 0.03
% 11.54/4.47  Main loop            : 3.30
% 11.54/4.47  Inferencing          : 1.53
% 11.54/4.47  Reduction            : 0.93
% 11.54/4.47  Demodulation         : 0.72
% 11.54/4.47  BG Simplification    : 0.11
% 11.54/4.47  Subsumption          : 0.60
% 11.54/4.47  Abstraction          : 0.23
% 11.54/4.47  MUC search           : 0.00
% 11.54/4.47  Cooper               : 0.00
% 11.54/4.47  Total                : 3.73
% 11.54/4.47  Index Insertion      : 0.00
% 11.54/4.47  Index Deletion       : 0.00
% 11.54/4.47  Index Matching       : 0.00
% 11.54/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
