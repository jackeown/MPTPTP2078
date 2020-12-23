%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:31 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 195 expanded)
%              Number of leaves         :   50 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 301 expanded)
%              Number of equality atoms :   32 (  79 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_172,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_148,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_94,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_96,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_70,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_155,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_144,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_121,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_84,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_136,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_162,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_84,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_82,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_72,plain,(
    ! [A_87] :
      ( k2_xboole_0(k1_relat_1(A_87),k2_relat_1(A_87)) = k3_relat_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_42,plain,(
    ! [B_38,A_37] : k2_tarski(B_38,A_37) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_148,plain,(
    ! [A_108,B_109] : k3_tarski(k2_tarski(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_163,plain,(
    ! [B_110,A_111] : k3_tarski(k2_tarski(B_110,A_111)) = k2_xboole_0(A_111,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_148])).

tff(c_44,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_211,plain,(
    ! [B_119,A_120] : k2_xboole_0(B_119,A_120) = k2_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_22,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    ! [A_120] : k2_xboole_0(k1_xboole_0,A_120) = A_120 ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_22])).

tff(c_169,plain,(
    ! [B_110,A_111] : k2_xboole_0(B_110,A_111) = k2_xboole_0(A_111,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_80,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1343,plain,(
    ! [A_215,B_216,C_217] :
      ( r1_tarski(k4_xboole_0(A_215,B_216),C_217)
      | ~ r1_tarski(A_215,k2_xboole_0(B_216,C_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_335,plain,(
    ! [B_126,A_127] :
      ( B_126 = A_127
      | ~ r1_tarski(B_126,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_357,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_335])).

tff(c_1362,plain,(
    ! [A_215,B_216] :
      ( k4_xboole_0(A_215,B_216) = k1_xboole_0
      | ~ r1_tarski(A_215,k2_xboole_0(B_216,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1343,c_357])).

tff(c_1387,plain,(
    ! [A_218,B_219] :
      ( k4_xboole_0(A_218,B_219) = k1_xboole_0
      | ~ r1_tarski(A_218,B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1362])).

tff(c_1471,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_1387])).

tff(c_30,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1504,plain,(
    k2_xboole_0('#skF_10',k1_xboole_0) = k2_xboole_0('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_30])).

tff(c_1523,plain,(
    k2_xboole_0('#skF_9','#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_22,c_1504])).

tff(c_3737,plain,(
    ! [A_276,B_277] :
      ( k2_xboole_0(k1_relat_1(A_276),k1_relat_1(B_277)) = k1_relat_1(k2_xboole_0(A_276,B_277))
      | ~ v1_relat_1(B_277)
      | ~ v1_relat_1(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10111,plain,(
    ! [A_406,B_407] :
      ( r1_tarski(k1_relat_1(A_406),k1_relat_1(k2_xboole_0(A_406,B_407)))
      | ~ v1_relat_1(B_407)
      | ~ v1_relat_1(A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3737,c_38])).

tff(c_10172,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_10111])).

tff(c_10212,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_10172])).

tff(c_1380,plain,(
    ! [A_215,B_216] :
      ( k4_xboole_0(A_215,B_216) = k1_xboole_0
      | ~ r1_tarski(A_215,B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1362])).

tff(c_10233,plain,(
    k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10212,c_1380])).

tff(c_1007,plain,(
    ! [A_196,B_197,C_198] :
      ( r1_tarski(A_196,k2_xboole_0(B_197,C_198))
      | ~ r1_tarski(k4_xboole_0(A_196,B_197),C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1064,plain,(
    ! [A_196,B_197,B_33] : r1_tarski(A_196,k2_xboole_0(B_197,k2_xboole_0(k4_xboole_0(A_196,B_197),B_33))) ),
    inference(resolution,[status(thm)],[c_38,c_1007])).

tff(c_10267,plain,(
    ! [B_33] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),k2_xboole_0(k1_xboole_0,B_33))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10233,c_1064])).

tff(c_10486,plain,(
    ! [B_408] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),B_408)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_10267])).

tff(c_10528,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_10486])).

tff(c_10560,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_10528])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4019,plain,(
    ! [A_283,C_284] :
      ( r2_hidden(k4_tarski('#skF_8'(A_283,k2_relat_1(A_283),C_284),C_284),A_283)
      | ~ r2_hidden(C_284,k2_relat_1(A_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    ! [A_41] : r2_hidden(A_41,'#skF_3'(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_719,plain,(
    ! [C_164,A_165,D_166] :
      ( r2_hidden(C_164,k2_relat_1(A_165))
      | ~ r2_hidden(k4_tarski(D_166,C_164),A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_724,plain,(
    ! [C_164,D_166] : r2_hidden(C_164,k2_relat_1('#skF_3'(k4_tarski(D_166,C_164)))) ),
    inference(resolution,[status(thm)],[c_52,c_719])).

tff(c_56,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_4'(A_59,B_60),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_731,plain,(
    ! [A_169,B_170,C_171] :
      ( ~ r1_xboole_0(A_169,B_170)
      | ~ r2_hidden(C_171,B_170)
      | ~ r2_hidden(C_171,A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_735,plain,(
    ! [C_172,A_173] :
      ( ~ r2_hidden(C_172,k1_xboole_0)
      | ~ r2_hidden(C_172,A_173) ) ),
    inference(resolution,[status(thm)],[c_36,c_731])).

tff(c_799,plain,(
    ! [A_176,A_177] :
      ( ~ r2_hidden('#skF_4'(A_176,k1_xboole_0),A_177)
      | ~ r2_hidden(A_176,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_735])).

tff(c_810,plain,(
    ! [A_176] : ~ r2_hidden(A_176,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_724,c_799])).

tff(c_4037,plain,(
    ! [C_285] : ~ r2_hidden(C_285,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4019,c_810])).

tff(c_4068,plain,(
    ! [B_286] : r1_tarski(k2_relat_1(k1_xboole_0),B_286) ),
    inference(resolution,[status(thm)],[c_6,c_4037])).

tff(c_4103,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4068,c_357])).

tff(c_58,plain,(
    ! [A_66,B_67] : k6_subset_1(A_66,B_67) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_76,plain,(
    ! [A_91,B_93] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_91),k2_relat_1(B_93)),k2_relat_1(k6_subset_1(A_91,B_93)))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4133,plain,(
    ! [A_287,B_288] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_287),k2_relat_1(B_288)),k2_relat_1(k4_xboole_0(A_287,B_288)))
      | ~ v1_relat_1(B_288)
      | ~ v1_relat_1(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_76])).

tff(c_4184,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_4133])).

tff(c_4213,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4103,c_4184])).

tff(c_4244,plain,(
    k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4213,c_357])).

tff(c_34,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,k2_xboole_0(B_29,C_30))
      | ~ r1_tarski(k4_xboole_0(A_28,B_29),C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4322,plain,(
    ! [C_30] :
      ( r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(k2_relat_1('#skF_10'),C_30))
      | ~ r1_tarski(k1_xboole_0,C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4244,c_34])).

tff(c_4422,plain,(
    ! [C_296] : r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(k2_relat_1('#skF_10'),C_296)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4322])).

tff(c_4644,plain,(
    ! [B_300] : r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(B_300,k2_relat_1('#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_4422])).

tff(c_4663,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4644])).

tff(c_4683,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4663])).

tff(c_2810,plain,(
    ! [A_245,C_246,B_247] :
      ( r1_tarski(k2_xboole_0(A_245,C_246),B_247)
      | ~ r1_tarski(C_246,B_247)
      | ~ r1_tarski(A_245,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14883,plain,(
    ! [A_492,B_493] :
      ( r1_tarski(k3_relat_1(A_492),B_493)
      | ~ r1_tarski(k2_relat_1(A_492),B_493)
      | ~ r1_tarski(k1_relat_1(A_492),B_493)
      | ~ v1_relat_1(A_492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2810])).

tff(c_78,plain,(
    ~ r1_tarski(k3_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_14955,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_14883,c_78])).

tff(c_14986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10560,c_4683,c_14955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.07/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/3.11  
% 8.07/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/3.11  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 8.07/3.11  
% 8.07/3.11  %Foreground sorts:
% 8.07/3.11  
% 8.07/3.11  
% 8.07/3.11  %Background operators:
% 8.07/3.11  
% 8.07/3.11  
% 8.07/3.11  %Foreground operators:
% 8.07/3.11  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.07/3.11  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 8.07/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.07/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.07/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.07/3.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.07/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.07/3.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.07/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.07/3.11  tff('#skF_10', type, '#skF_10': $i).
% 8.07/3.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.07/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.07/3.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.07/3.11  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.07/3.11  tff('#skF_9', type, '#skF_9': $i).
% 8.07/3.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.07/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.07/3.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.07/3.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.07/3.11  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.07/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.07/3.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.07/3.11  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 8.07/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.07/3.11  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.07/3.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.07/3.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.07/3.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.07/3.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.07/3.11  
% 8.27/3.13  tff(f_172, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 8.27/3.13  tff(f_148, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.27/3.13  tff(f_94, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.27/3.13  tff(f_96, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.27/3.13  tff(f_62, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.27/3.13  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.27/3.13  tff(f_70, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.27/3.13  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.27/3.13  tff(f_74, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.27/3.13  tff(f_155, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 8.27/3.13  tff(f_86, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.27/3.13  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.27/3.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.27/3.13  tff(f_144, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.27/3.13  tff(f_121, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 8.27/3.13  tff(f_134, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 8.27/3.13  tff(f_84, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.27/3.13  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.27/3.13  tff(f_136, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.27/3.13  tff(f_162, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 8.27/3.13  tff(f_92, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.27/3.13  tff(c_84, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.27/3.13  tff(c_82, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.27/3.13  tff(c_72, plain, (![A_87]: (k2_xboole_0(k1_relat_1(A_87), k2_relat_1(A_87))=k3_relat_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.27/3.13  tff(c_42, plain, (![B_38, A_37]: (k2_tarski(B_38, A_37)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.27/3.13  tff(c_148, plain, (![A_108, B_109]: (k3_tarski(k2_tarski(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.27/3.13  tff(c_163, plain, (![B_110, A_111]: (k3_tarski(k2_tarski(B_110, A_111))=k2_xboole_0(A_111, B_110))), inference(superposition, [status(thm), theory('equality')], [c_42, c_148])).
% 8.27/3.13  tff(c_44, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.27/3.13  tff(c_211, plain, (![B_119, A_120]: (k2_xboole_0(B_119, A_120)=k2_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_163, c_44])).
% 8.27/3.13  tff(c_22, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.27/3.13  tff(c_239, plain, (![A_120]: (k2_xboole_0(k1_xboole_0, A_120)=A_120)), inference(superposition, [status(thm), theory('equality')], [c_211, c_22])).
% 8.27/3.13  tff(c_169, plain, (![B_110, A_111]: (k2_xboole_0(B_110, A_111)=k2_xboole_0(A_111, B_110))), inference(superposition, [status(thm), theory('equality')], [c_163, c_44])).
% 8.27/3.13  tff(c_80, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.27/3.13  tff(c_1343, plain, (![A_215, B_216, C_217]: (r1_tarski(k4_xboole_0(A_215, B_216), C_217) | ~r1_tarski(A_215, k2_xboole_0(B_216, C_217)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.27/3.13  tff(c_26, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.27/3.13  tff(c_335, plain, (![B_126, A_127]: (B_126=A_127 | ~r1_tarski(B_126, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.27/3.13  tff(c_357, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_335])).
% 8.27/3.13  tff(c_1362, plain, (![A_215, B_216]: (k4_xboole_0(A_215, B_216)=k1_xboole_0 | ~r1_tarski(A_215, k2_xboole_0(B_216, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1343, c_357])).
% 8.27/3.13  tff(c_1387, plain, (![A_218, B_219]: (k4_xboole_0(A_218, B_219)=k1_xboole_0 | ~r1_tarski(A_218, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1362])).
% 8.27/3.13  tff(c_1471, plain, (k4_xboole_0('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_1387])).
% 8.27/3.13  tff(c_30, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.27/3.13  tff(c_1504, plain, (k2_xboole_0('#skF_10', k1_xboole_0)=k2_xboole_0('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_30])).
% 8.27/3.13  tff(c_1523, plain, (k2_xboole_0('#skF_9', '#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_22, c_1504])).
% 8.27/3.13  tff(c_3737, plain, (![A_276, B_277]: (k2_xboole_0(k1_relat_1(A_276), k1_relat_1(B_277))=k1_relat_1(k2_xboole_0(A_276, B_277)) | ~v1_relat_1(B_277) | ~v1_relat_1(A_276))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.27/3.13  tff(c_38, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.27/3.13  tff(c_10111, plain, (![A_406, B_407]: (r1_tarski(k1_relat_1(A_406), k1_relat_1(k2_xboole_0(A_406, B_407))) | ~v1_relat_1(B_407) | ~v1_relat_1(A_406))), inference(superposition, [status(thm), theory('equality')], [c_3737, c_38])).
% 8.27/3.13  tff(c_10172, plain, (r1_tarski(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1523, c_10111])).
% 8.27/3.13  tff(c_10212, plain, (r1_tarski(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_10172])).
% 8.27/3.13  tff(c_1380, plain, (![A_215, B_216]: (k4_xboole_0(A_215, B_216)=k1_xboole_0 | ~r1_tarski(A_215, B_216))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1362])).
% 8.27/3.13  tff(c_10233, plain, (k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10212, c_1380])).
% 8.27/3.13  tff(c_1007, plain, (![A_196, B_197, C_198]: (r1_tarski(A_196, k2_xboole_0(B_197, C_198)) | ~r1_tarski(k4_xboole_0(A_196, B_197), C_198))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.27/3.13  tff(c_1064, plain, (![A_196, B_197, B_33]: (r1_tarski(A_196, k2_xboole_0(B_197, k2_xboole_0(k4_xboole_0(A_196, B_197), B_33))))), inference(resolution, [status(thm)], [c_38, c_1007])).
% 8.27/3.13  tff(c_10267, plain, (![B_33]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), k2_xboole_0(k1_xboole_0, B_33))))), inference(superposition, [status(thm), theory('equality')], [c_10233, c_1064])).
% 8.27/3.13  tff(c_10486, plain, (![B_408]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), B_408)))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_10267])).
% 8.27/3.13  tff(c_10528, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_72, c_10486])).
% 8.27/3.13  tff(c_10560, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_10528])).
% 8.27/3.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.27/3.13  tff(c_4019, plain, (![A_283, C_284]: (r2_hidden(k4_tarski('#skF_8'(A_283, k2_relat_1(A_283), C_284), C_284), A_283) | ~r2_hidden(C_284, k2_relat_1(A_283)))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.27/3.13  tff(c_52, plain, (![A_41]: (r2_hidden(A_41, '#skF_3'(A_41)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.27/3.13  tff(c_719, plain, (![C_164, A_165, D_166]: (r2_hidden(C_164, k2_relat_1(A_165)) | ~r2_hidden(k4_tarski(D_166, C_164), A_165))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.27/3.13  tff(c_724, plain, (![C_164, D_166]: (r2_hidden(C_164, k2_relat_1('#skF_3'(k4_tarski(D_166, C_164)))))), inference(resolution, [status(thm)], [c_52, c_719])).
% 8.27/3.13  tff(c_56, plain, (![A_59, B_60]: (r2_hidden('#skF_4'(A_59, B_60), B_60) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.27/3.13  tff(c_36, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.27/3.13  tff(c_731, plain, (![A_169, B_170, C_171]: (~r1_xboole_0(A_169, B_170) | ~r2_hidden(C_171, B_170) | ~r2_hidden(C_171, A_169))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.27/3.13  tff(c_735, plain, (![C_172, A_173]: (~r2_hidden(C_172, k1_xboole_0) | ~r2_hidden(C_172, A_173))), inference(resolution, [status(thm)], [c_36, c_731])).
% 8.27/3.13  tff(c_799, plain, (![A_176, A_177]: (~r2_hidden('#skF_4'(A_176, k1_xboole_0), A_177) | ~r2_hidden(A_176, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_735])).
% 8.27/3.13  tff(c_810, plain, (![A_176]: (~r2_hidden(A_176, k1_xboole_0))), inference(resolution, [status(thm)], [c_724, c_799])).
% 8.27/3.13  tff(c_4037, plain, (![C_285]: (~r2_hidden(C_285, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4019, c_810])).
% 8.27/3.13  tff(c_4068, plain, (![B_286]: (r1_tarski(k2_relat_1(k1_xboole_0), B_286))), inference(resolution, [status(thm)], [c_6, c_4037])).
% 8.27/3.13  tff(c_4103, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4068, c_357])).
% 8.27/3.13  tff(c_58, plain, (![A_66, B_67]: (k6_subset_1(A_66, B_67)=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.27/3.13  tff(c_76, plain, (![A_91, B_93]: (r1_tarski(k6_subset_1(k2_relat_1(A_91), k2_relat_1(B_93)), k2_relat_1(k6_subset_1(A_91, B_93))) | ~v1_relat_1(B_93) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.27/3.13  tff(c_4133, plain, (![A_287, B_288]: (r1_tarski(k4_xboole_0(k2_relat_1(A_287), k2_relat_1(B_288)), k2_relat_1(k4_xboole_0(A_287, B_288))) | ~v1_relat_1(B_288) | ~v1_relat_1(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_76])).
% 8.27/3.13  tff(c_4184, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_4133])).
% 8.27/3.13  tff(c_4213, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_4103, c_4184])).
% 8.27/3.13  tff(c_4244, plain, (k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4213, c_357])).
% 8.27/3.13  tff(c_34, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, k2_xboole_0(B_29, C_30)) | ~r1_tarski(k4_xboole_0(A_28, B_29), C_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.27/3.13  tff(c_4322, plain, (![C_30]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(k2_relat_1('#skF_10'), C_30)) | ~r1_tarski(k1_xboole_0, C_30))), inference(superposition, [status(thm), theory('equality')], [c_4244, c_34])).
% 8.27/3.13  tff(c_4422, plain, (![C_296]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(k2_relat_1('#skF_10'), C_296)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4322])).
% 8.27/3.13  tff(c_4644, plain, (![B_300]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(B_300, k2_relat_1('#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_169, c_4422])).
% 8.27/3.13  tff(c_4663, plain, (r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_72, c_4644])).
% 8.27/3.13  tff(c_4683, plain, (r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4663])).
% 8.27/3.13  tff(c_2810, plain, (![A_245, C_246, B_247]: (r1_tarski(k2_xboole_0(A_245, C_246), B_247) | ~r1_tarski(C_246, B_247) | ~r1_tarski(A_245, B_247))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.27/3.13  tff(c_14883, plain, (![A_492, B_493]: (r1_tarski(k3_relat_1(A_492), B_493) | ~r1_tarski(k2_relat_1(A_492), B_493) | ~r1_tarski(k1_relat_1(A_492), B_493) | ~v1_relat_1(A_492))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2810])).
% 8.27/3.13  tff(c_78, plain, (~r1_tarski(k3_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.27/3.13  tff(c_14955, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_14883, c_78])).
% 8.27/3.13  tff(c_14986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_10560, c_4683, c_14955])).
% 8.27/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.27/3.13  
% 8.27/3.13  Inference rules
% 8.27/3.13  ----------------------
% 8.27/3.13  #Ref     : 0
% 8.27/3.13  #Sup     : 3701
% 8.27/3.13  #Fact    : 0
% 8.27/3.13  #Define  : 0
% 8.27/3.13  #Split   : 9
% 8.27/3.13  #Chain   : 0
% 8.27/3.13  #Close   : 0
% 8.27/3.13  
% 8.27/3.13  Ordering : KBO
% 8.27/3.13  
% 8.27/3.13  Simplification rules
% 8.27/3.13  ----------------------
% 8.27/3.13  #Subsume      : 457
% 8.27/3.13  #Demod        : 2540
% 8.27/3.13  #Tautology    : 1911
% 8.27/3.13  #SimpNegUnit  : 2
% 8.27/3.13  #BackRed      : 4
% 8.27/3.13  
% 8.27/3.13  #Partial instantiations: 0
% 8.27/3.13  #Strategies tried      : 1
% 8.27/3.13  
% 8.27/3.13  Timing (in seconds)
% 8.27/3.13  ----------------------
% 8.27/3.13  Preprocessing        : 0.39
% 8.27/3.13  Parsing              : 0.20
% 8.27/3.13  CNF conversion       : 0.04
% 8.27/3.13  Main loop            : 1.96
% 8.27/3.13  Inferencing          : 0.44
% 8.27/3.13  Reduction            : 0.92
% 8.27/3.13  Demodulation         : 0.74
% 8.27/3.13  BG Simplification    : 0.05
% 8.27/3.13  Subsumption          : 0.43
% 8.27/3.13  Abstraction          : 0.07
% 8.27/3.14  MUC search           : 0.00
% 8.27/3.14  Cooper               : 0.00
% 8.27/3.14  Total                : 2.40
% 8.27/3.14  Index Insertion      : 0.00
% 8.27/3.14  Index Deletion       : 0.00
% 8.27/3.14  Index Matching       : 0.00
% 8.27/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
