%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:48 EST 2020

% Result     : Theorem 43.86s
% Output     : CNFRefutation 43.86s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 340 expanded)
%              Number of leaves         :   27 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 661 expanded)
%              Number of equality atoms :   46 ( 147 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1782,plain,(
    ! [B_129,A_130] :
      ( k1_relat_1(k7_relat_1(B_129,A_130)) = A_130
      | ~ r1_tarski(A_130,k1_relat_1(B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1799,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1782])).

tff(c_1812,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1799])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1847,plain,(
    ! [A_20] :
      ( r1_tarski(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_20),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_22])).

tff(c_10634,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1847])).

tff(c_10637,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_10634])).

tff(c_10641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10637])).

tff(c_10643,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1847])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_28,A_27)),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_353,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ r1_tarski(k1_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10950,plain,(
    ! [B_297,A_298] :
      ( k7_relat_1(k7_relat_1(B_297,A_298),A_298) = k7_relat_1(B_297,A_298)
      | ~ v1_relat_1(k7_relat_1(B_297,A_298))
      | ~ v1_relat_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_30,c_353])).

tff(c_10952,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10643,c_10950])).

tff(c_10973,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10952])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_32,plain,(
    ! [B_30,A_29] :
      ( k3_xboole_0(k1_relat_1(B_30),A_29) = k1_relat_1(k7_relat_1(B_30,A_29))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1117,plain,(
    ! [B_109,A_110] :
      ( k7_relat_1(B_109,k3_xboole_0(k1_relat_1(B_109),A_110)) = k7_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9055,plain,(
    ! [B_269,A_270] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_269,A_270)),k3_xboole_0(k1_relat_1(B_269),A_270))
      | ~ v1_relat_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_30])).

tff(c_9105,plain,
    ( r1_tarski('#skF_1',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_9055])).

tff(c_9134,plain,(
    r1_tarski('#skF_1',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_9105])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9151,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9134,c_12])).

tff(c_9895,plain,
    ( k2_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9151])).

tff(c_9917,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_63,c_1812,c_9895])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10556,plain,(
    ! [B_292,A_293] :
      ( k9_relat_1(B_292,k3_xboole_0(k1_relat_1(B_292),A_293)) = k2_relat_1(k7_relat_1(B_292,A_293))
      | ~ v1_relat_1(B_292)
      | ~ v1_relat_1(B_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_20])).

tff(c_10568,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9917,c_10556])).

tff(c_10599,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_10568])).

tff(c_11008,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10973,c_20])).

tff(c_11036,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_10599,c_11008])).

tff(c_319,plain,(
    ! [B_70,A_71] :
      ( k2_relat_1(k7_relat_1(B_70,A_71)) = k9_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17784,plain,(
    ! [B_394,A_395] :
      ( k10_relat_1(k7_relat_1(B_394,A_395),k9_relat_1(B_394,A_395)) = k1_relat_1(k7_relat_1(B_394,A_395))
      | ~ v1_relat_1(k7_relat_1(B_394,A_395))
      | ~ v1_relat_1(B_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_24])).

tff(c_17868,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10973,c_17784])).

tff(c_17925,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_10643,c_10973,c_1812,c_10973,c_11036,c_17868])).

tff(c_1832,plain,(
    ! [A_29] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_29)) = k3_xboole_0('#skF_1',A_29)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_32])).

tff(c_20401,plain,(
    ! [A_29] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_29)) = k3_xboole_0('#skF_1',A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_1832])).

tff(c_2542,plain,(
    ! [A_144,C_145,B_146] :
      ( k3_xboole_0(A_144,k10_relat_1(C_145,B_146)) = k10_relat_1(k7_relat_1(C_145,A_144),B_146)
      | ~ v1_relat_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,k3_xboole_0(k1_relat_1(B_26),A_25)) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16979,plain,(
    ! [B_385,C_386,B_387] :
      ( k7_relat_1(B_385,k10_relat_1(k7_relat_1(C_386,k1_relat_1(B_385)),B_387)) = k7_relat_1(B_385,k10_relat_1(C_386,B_387))
      | ~ v1_relat_1(B_385)
      | ~ v1_relat_1(C_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2542,c_28])).

tff(c_17053,plain,(
    ! [C_386,B_387] :
      ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_386,'#skF_1'),B_387)) = k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(C_386,B_387))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(C_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_16979])).

tff(c_112279,plain,(
    ! [C_1131,B_1132] :
      ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_1131,'#skF_1'),B_1132)) = k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(C_1131,B_1132))
      | ~ v1_relat_1(C_1131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_17053])).

tff(c_1809,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,k10_relat_1(B_21,A_20))) = k10_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_1782])).

tff(c_112358,plain,(
    ! [B_1132] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1('#skF_2',B_1132))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),B_1132)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112279,c_1809])).

tff(c_137631,plain,(
    ! [B_1246] : k3_xboole_0('#skF_1',k10_relat_1('#skF_2',B_1246)) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),B_1246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10643,c_20401,c_112358])).

tff(c_20402,plain,(
    ! [A_428] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_428)) = k3_xboole_0('#skF_1',A_428) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_1832])).

tff(c_20526,plain,(
    ! [A_428] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_428),A_428)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20402,c_30])).

tff(c_20631,plain,(
    ! [A_428] : r1_tarski(k3_xboole_0('#skF_1',A_428),A_428) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10643,c_20526])).

tff(c_137815,plain,(
    ! [B_1247] : r1_tarski(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),B_1247),k10_relat_1('#skF_2',B_1247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137631,c_20631])).

tff(c_137861,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17925,c_137815])).

tff(c_137907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_137861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.86/32.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.86/32.02  
% 43.86/32.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.86/32.02  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 43.86/32.02  
% 43.86/32.02  %Foreground sorts:
% 43.86/32.02  
% 43.86/32.02  
% 43.86/32.02  %Background operators:
% 43.86/32.02  
% 43.86/32.02  
% 43.86/32.02  %Foreground operators:
% 43.86/32.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.86/32.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 43.86/32.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.86/32.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 43.86/32.02  tff('#skF_2', type, '#skF_2': $i).
% 43.86/32.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 43.86/32.02  tff('#skF_1', type, '#skF_1': $i).
% 43.86/32.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.86/32.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 43.86/32.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 43.86/32.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.86/32.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.86/32.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.86/32.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 43.86/32.02  
% 43.86/32.04  tff(f_110, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 43.86/32.04  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 43.86/32.04  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 43.86/32.04  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 43.86/32.04  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 43.86/32.04  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 43.86/32.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 43.86/32.04  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 43.86/32.04  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 43.86/32.04  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 43.86/32.04  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 43.86/32.04  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 43.86/32.04  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 43.86/32.04  tff(c_42, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.86/32.04  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.86/32.04  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 43.86/32.04  tff(c_44, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 43.86/32.04  tff(c_1782, plain, (![B_129, A_130]: (k1_relat_1(k7_relat_1(B_129, A_130))=A_130 | ~r1_tarski(A_130, k1_relat_1(B_129)) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_89])).
% 43.86/32.04  tff(c_1799, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1782])).
% 43.86/32.04  tff(c_1812, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1799])).
% 43.86/32.04  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.86/32.04  tff(c_1847, plain, (![A_20]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_20), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1812, c_22])).
% 43.86/32.04  tff(c_10634, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1847])).
% 43.86/32.04  tff(c_10637, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_10634])).
% 43.86/32.04  tff(c_10641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_10637])).
% 43.86/32.04  tff(c_10643, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_1847])).
% 43.86/32.04  tff(c_30, plain, (![B_28, A_27]: (r1_tarski(k1_relat_1(k7_relat_1(B_28, A_27)), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 43.86/32.04  tff(c_353, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~r1_tarski(k1_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_95])).
% 43.86/32.04  tff(c_10950, plain, (![B_297, A_298]: (k7_relat_1(k7_relat_1(B_297, A_298), A_298)=k7_relat_1(B_297, A_298) | ~v1_relat_1(k7_relat_1(B_297, A_298)) | ~v1_relat_1(B_297))), inference(resolution, [status(thm)], [c_30, c_353])).
% 43.86/32.04  tff(c_10952, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10643, c_10950])).
% 43.86/32.04  tff(c_10973, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10952])).
% 43.86/32.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 43.86/32.04  tff(c_51, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.86/32.04  tff(c_63, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_51])).
% 43.86/32.04  tff(c_32, plain, (![B_30, A_29]: (k3_xboole_0(k1_relat_1(B_30), A_29)=k1_relat_1(k7_relat_1(B_30, A_29)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 43.86/32.04  tff(c_1117, plain, (![B_109, A_110]: (k7_relat_1(B_109, k3_xboole_0(k1_relat_1(B_109), A_110))=k7_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_75])).
% 43.86/32.04  tff(c_9055, plain, (![B_269, A_270]: (r1_tarski(k1_relat_1(k7_relat_1(B_269, A_270)), k3_xboole_0(k1_relat_1(B_269), A_270)) | ~v1_relat_1(B_269) | ~v1_relat_1(B_269))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_30])).
% 43.86/32.04  tff(c_9105, plain, (r1_tarski('#skF_1', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1812, c_9055])).
% 43.86/32.04  tff(c_9134, plain, (r1_tarski('#skF_1', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_9105])).
% 43.86/32.04  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 43.86/32.04  tff(c_9151, plain, (k2_xboole_0('#skF_1', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_9134, c_12])).
% 43.86/32.04  tff(c_9895, plain, (k2_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_9151])).
% 43.86/32.04  tff(c_9917, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_63, c_1812, c_9895])).
% 43.86/32.04  tff(c_20, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 43.86/32.04  tff(c_10556, plain, (![B_292, A_293]: (k9_relat_1(B_292, k3_xboole_0(k1_relat_1(B_292), A_293))=k2_relat_1(k7_relat_1(B_292, A_293)) | ~v1_relat_1(B_292) | ~v1_relat_1(B_292))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_20])).
% 43.86/32.04  tff(c_10568, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9917, c_10556])).
% 43.86/32.04  tff(c_10599, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_10568])).
% 43.86/32.04  tff(c_11008, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10973, c_20])).
% 43.86/32.04  tff(c_11036, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_10599, c_11008])).
% 43.86/32.04  tff(c_319, plain, (![B_70, A_71]: (k2_relat_1(k7_relat_1(B_70, A_71))=k9_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 43.86/32.04  tff(c_24, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 43.86/32.04  tff(c_17784, plain, (![B_394, A_395]: (k10_relat_1(k7_relat_1(B_394, A_395), k9_relat_1(B_394, A_395))=k1_relat_1(k7_relat_1(B_394, A_395)) | ~v1_relat_1(k7_relat_1(B_394, A_395)) | ~v1_relat_1(B_394))), inference(superposition, [status(thm), theory('equality')], [c_319, c_24])).
% 43.86/32.04  tff(c_17868, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10973, c_17784])).
% 43.86/32.04  tff(c_17925, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_10643, c_10973, c_1812, c_10973, c_11036, c_17868])).
% 43.86/32.04  tff(c_1832, plain, (![A_29]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_29))=k3_xboole_0('#skF_1', A_29) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1812, c_32])).
% 43.86/32.04  tff(c_20401, plain, (![A_29]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_29))=k3_xboole_0('#skF_1', A_29))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_1832])).
% 43.86/32.04  tff(c_2542, plain, (![A_144, C_145, B_146]: (k3_xboole_0(A_144, k10_relat_1(C_145, B_146))=k10_relat_1(k7_relat_1(C_145, A_144), B_146) | ~v1_relat_1(C_145))), inference(cnfTransformation, [status(thm)], [f_103])).
% 43.86/32.04  tff(c_28, plain, (![B_26, A_25]: (k7_relat_1(B_26, k3_xboole_0(k1_relat_1(B_26), A_25))=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 43.86/32.04  tff(c_16979, plain, (![B_385, C_386, B_387]: (k7_relat_1(B_385, k10_relat_1(k7_relat_1(C_386, k1_relat_1(B_385)), B_387))=k7_relat_1(B_385, k10_relat_1(C_386, B_387)) | ~v1_relat_1(B_385) | ~v1_relat_1(C_386))), inference(superposition, [status(thm), theory('equality')], [c_2542, c_28])).
% 43.86/32.04  tff(c_17053, plain, (![C_386, B_387]: (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_386, '#skF_1'), B_387))=k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(C_386, B_387)) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(C_386))), inference(superposition, [status(thm), theory('equality')], [c_1812, c_16979])).
% 43.86/32.04  tff(c_112279, plain, (![C_1131, B_1132]: (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_1131, '#skF_1'), B_1132))=k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(C_1131, B_1132)) | ~v1_relat_1(C_1131))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_17053])).
% 43.86/32.04  tff(c_1809, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, k10_relat_1(B_21, A_20)))=k10_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_22, c_1782])).
% 43.86/32.04  tff(c_112358, plain, (![B_1132]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1('#skF_2', B_1132)))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), B_1132) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_112279, c_1809])).
% 43.86/32.04  tff(c_137631, plain, (![B_1246]: (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', B_1246))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), B_1246))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10643, c_20401, c_112358])).
% 43.86/32.04  tff(c_20402, plain, (![A_428]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_428))=k3_xboole_0('#skF_1', A_428))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_1832])).
% 43.86/32.04  tff(c_20526, plain, (![A_428]: (r1_tarski(k3_xboole_0('#skF_1', A_428), A_428) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_20402, c_30])).
% 43.86/32.04  tff(c_20631, plain, (![A_428]: (r1_tarski(k3_xboole_0('#skF_1', A_428), A_428))), inference(demodulation, [status(thm), theory('equality')], [c_10643, c_20526])).
% 43.86/32.04  tff(c_137815, plain, (![B_1247]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), B_1247), k10_relat_1('#skF_2', B_1247)))), inference(superposition, [status(thm), theory('equality')], [c_137631, c_20631])).
% 43.86/32.04  tff(c_137861, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17925, c_137815])).
% 43.86/32.04  tff(c_137907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_137861])).
% 43.86/32.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.86/32.04  
% 43.86/32.04  Inference rules
% 43.86/32.04  ----------------------
% 43.86/32.04  #Ref     : 0
% 43.86/32.04  #Sup     : 34869
% 43.86/32.04  #Fact    : 0
% 43.86/32.04  #Define  : 0
% 43.86/32.04  #Split   : 11
% 43.86/32.04  #Chain   : 0
% 43.86/32.04  #Close   : 0
% 43.86/32.04  
% 43.86/32.04  Ordering : KBO
% 43.86/32.04  
% 43.86/32.04  Simplification rules
% 43.86/32.04  ----------------------
% 43.86/32.04  #Subsume      : 8001
% 43.86/32.04  #Demod        : 23279
% 43.86/32.04  #Tautology    : 12717
% 43.86/32.04  #SimpNegUnit  : 13
% 43.86/32.04  #BackRed      : 79
% 43.86/32.04  
% 43.86/32.04  #Partial instantiations: 0
% 43.86/32.04  #Strategies tried      : 1
% 43.86/32.04  
% 43.86/32.04  Timing (in seconds)
% 43.86/32.04  ----------------------
% 44.04/32.04  Preprocessing        : 0.52
% 44.04/32.04  Parsing              : 0.27
% 44.04/32.04  CNF conversion       : 0.03
% 44.04/32.04  Main loop            : 30.65
% 44.04/32.04  Inferencing          : 3.11
% 44.04/32.04  Reduction            : 15.44
% 44.04/32.04  Demodulation         : 13.95
% 44.04/32.04  BG Simplification    : 0.43
% 44.04/32.04  Subsumption          : 10.41
% 44.04/32.04  Abstraction          : 0.68
% 44.04/32.04  MUC search           : 0.00
% 44.04/32.04  Cooper               : 0.00
% 44.04/32.04  Total                : 31.21
% 44.04/32.04  Index Insertion      : 0.00
% 44.04/32.04  Index Deletion       : 0.00
% 44.04/32.04  Index Matching       : 0.00
% 44.04/32.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
