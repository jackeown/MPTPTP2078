%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:14 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 167 expanded)
%              Number of equality atoms :   13 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(B_46,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_16,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [B_46,A_45] : k3_xboole_0(B_46,A_45) = k3_xboole_0(A_45,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_16])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_253,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(B_58)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_20,c_246])).

tff(c_266,plain,(
    ! [A_59,B_60] :
      ( v1_relat_1(k3_xboole_0(A_59,B_60))
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_4,c_253])).

tff(c_269,plain,(
    ! [B_46,A_45] :
      ( v1_relat_1(k3_xboole_0(B_46,A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_266])).

tff(c_82,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_3835,plain,(
    ! [A_153,B_154] :
      ( k2_xboole_0(k1_relat_1(A_153),k1_relat_1(B_154)) = k1_relat_1(k2_xboole_0(A_153,B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4523,plain,(
    ! [A_173,B_174] :
      ( r1_tarski(k1_relat_1(A_173),k1_relat_1(k2_xboole_0(A_173,B_174)))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3835,c_8])).

tff(c_6455,plain,(
    ! [A_210,B_211] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_210,B_211)),k1_relat_1(A_210))
      | ~ v1_relat_1(A_210)
      | ~ v1_relat_1(k3_xboole_0(A_210,B_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4523])).

tff(c_12905,plain,(
    ! [A_269,B_270] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_269,B_270)),k1_relat_1(B_270))
      | ~ v1_relat_1(B_270)
      | ~ v1_relat_1(k3_xboole_0(B_270,A_269)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_6455])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_435,plain,(
    ! [A_75,B_76] :
      ( k2_xboole_0(k1_relat_1(A_75),k1_relat_1(B_76)) = k1_relat_1(k2_xboole_0(A_75,B_76))
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1078,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k1_relat_1(A_96),k1_relat_1(k2_xboole_0(A_96,B_97)))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_8])).

tff(c_3591,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_143,B_144)),k1_relat_1(A_143))
      | ~ v1_relat_1(A_143)
      | ~ v1_relat_1(k3_xboole_0(A_143,B_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_1078])).

tff(c_280,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(A_63,k3_xboole_0(B_64,C_65))
      | ~ r1_tarski(A_63,C_65)
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_297,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_280,c_26])).

tff(c_306,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_3600,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3591,c_306])).

tff(c_3651,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3600])).

tff(c_3668,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_269,c_3651])).

tff(c_3675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3668])).

tff(c_3676,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_12914,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12905,c_3676])).

tff(c_12995,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_28,c_12914])).

tff(c_13022,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_269,c_12995])).

tff(c_13029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_13022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.85/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.96  
% 7.85/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.96  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.85/2.96  
% 7.85/2.96  %Foreground sorts:
% 7.85/2.96  
% 7.85/2.96  
% 7.85/2.96  %Background operators:
% 7.85/2.96  
% 7.85/2.96  
% 7.85/2.96  %Foreground operators:
% 7.85/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.85/2.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.85/2.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.85/2.96  tff('#skF_2', type, '#skF_2': $i).
% 7.85/2.96  tff('#skF_1', type, '#skF_1': $i).
% 7.85/2.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.85/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.85/2.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.85/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.85/2.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.85/2.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.85/2.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.85/2.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.85/2.96  
% 7.85/2.97  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 7.85/2.97  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.85/2.97  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.85/2.97  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.85/2.97  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.85/2.97  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.85/2.97  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.85/2.97  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 7.85/2.97  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.85/2.97  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.85/2.97  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.85/2.97  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.85/2.97  tff(c_66, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.85/2.97  tff(c_124, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(B_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_10, c_66])).
% 7.85/2.97  tff(c_16, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.85/2.97  tff(c_130, plain, (![B_46, A_45]: (k3_xboole_0(B_46, A_45)=k3_xboole_0(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_124, c_16])).
% 7.85/2.97  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.85/2.97  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.85/2.97  tff(c_246, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.85/2.97  tff(c_253, plain, (![A_57, B_58]: (v1_relat_1(A_57) | ~v1_relat_1(B_58) | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_20, c_246])).
% 7.85/2.97  tff(c_266, plain, (![A_59, B_60]: (v1_relat_1(k3_xboole_0(A_59, B_60)) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_4, c_253])).
% 7.85/2.97  tff(c_269, plain, (![B_46, A_45]: (v1_relat_1(k3_xboole_0(B_46, A_45)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_130, c_266])).
% 7.85/2.97  tff(c_82, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.85/2.97  tff(c_89, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_82])).
% 7.85/2.97  tff(c_3835, plain, (![A_153, B_154]: (k2_xboole_0(k1_relat_1(A_153), k1_relat_1(B_154))=k1_relat_1(k2_xboole_0(A_153, B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.85/2.97  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.85/2.97  tff(c_4523, plain, (![A_173, B_174]: (r1_tarski(k1_relat_1(A_173), k1_relat_1(k2_xboole_0(A_173, B_174))) | ~v1_relat_1(B_174) | ~v1_relat_1(A_173))), inference(superposition, [status(thm), theory('equality')], [c_3835, c_8])).
% 7.85/2.97  tff(c_6455, plain, (![A_210, B_211]: (r1_tarski(k1_relat_1(k3_xboole_0(A_210, B_211)), k1_relat_1(A_210)) | ~v1_relat_1(A_210) | ~v1_relat_1(k3_xboole_0(A_210, B_211)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4523])).
% 7.85/2.97  tff(c_12905, plain, (![A_269, B_270]: (r1_tarski(k1_relat_1(k3_xboole_0(A_269, B_270)), k1_relat_1(B_270)) | ~v1_relat_1(B_270) | ~v1_relat_1(k3_xboole_0(B_270, A_269)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_6455])).
% 7.85/2.97  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.85/2.97  tff(c_435, plain, (![A_75, B_76]: (k2_xboole_0(k1_relat_1(A_75), k1_relat_1(B_76))=k1_relat_1(k2_xboole_0(A_75, B_76)) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.85/2.97  tff(c_1078, plain, (![A_96, B_97]: (r1_tarski(k1_relat_1(A_96), k1_relat_1(k2_xboole_0(A_96, B_97))) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_435, c_8])).
% 7.85/2.97  tff(c_3591, plain, (![A_143, B_144]: (r1_tarski(k1_relat_1(k3_xboole_0(A_143, B_144)), k1_relat_1(A_143)) | ~v1_relat_1(A_143) | ~v1_relat_1(k3_xboole_0(A_143, B_144)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_1078])).
% 7.85/2.97  tff(c_280, plain, (![A_63, B_64, C_65]: (r1_tarski(A_63, k3_xboole_0(B_64, C_65)) | ~r1_tarski(A_63, C_65) | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.85/2.97  tff(c_26, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.85/2.97  tff(c_297, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_280, c_26])).
% 7.85/2.97  tff(c_306, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_297])).
% 7.85/2.97  tff(c_3600, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3591, c_306])).
% 7.85/2.97  tff(c_3651, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3600])).
% 7.85/2.97  tff(c_3668, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_269, c_3651])).
% 7.85/2.97  tff(c_3675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3668])).
% 7.85/2.97  tff(c_3676, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_297])).
% 7.85/2.97  tff(c_12914, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_12905, c_3676])).
% 7.85/2.97  tff(c_12995, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_28, c_12914])).
% 7.85/2.97  tff(c_13022, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_269, c_12995])).
% 7.85/2.97  tff(c_13029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_13022])).
% 7.85/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.97  
% 7.85/2.97  Inference rules
% 7.85/2.97  ----------------------
% 7.85/2.97  #Ref     : 0
% 7.85/2.97  #Sup     : 3342
% 7.85/2.97  #Fact    : 0
% 7.85/2.97  #Define  : 0
% 7.85/2.97  #Split   : 3
% 7.85/2.97  #Chain   : 0
% 7.85/2.97  #Close   : 0
% 7.85/2.97  
% 7.85/2.97  Ordering : KBO
% 7.85/2.97  
% 7.85/2.97  Simplification rules
% 7.85/2.97  ----------------------
% 7.85/2.97  #Subsume      : 500
% 7.85/2.97  #Demod        : 4461
% 7.85/2.97  #Tautology    : 2179
% 7.85/2.97  #SimpNegUnit  : 3
% 7.85/2.97  #BackRed      : 0
% 7.85/2.97  
% 7.85/2.97  #Partial instantiations: 0
% 7.85/2.97  #Strategies tried      : 1
% 7.85/2.97  
% 7.85/2.97  Timing (in seconds)
% 7.85/2.97  ----------------------
% 7.85/2.97  Preprocessing        : 0.36
% 7.85/2.97  Parsing              : 0.20
% 7.85/2.97  CNF conversion       : 0.02
% 7.85/2.97  Main loop            : 1.80
% 7.85/2.97  Inferencing          : 0.45
% 7.85/2.97  Reduction            : 0.99
% 7.85/2.97  Demodulation         : 0.87
% 7.85/2.97  BG Simplification    : 0.05
% 7.85/2.97  Subsumption          : 0.24
% 7.85/2.97  Abstraction          : 0.10
% 7.85/2.97  MUC search           : 0.00
% 7.85/2.97  Cooper               : 0.00
% 7.85/2.97  Total                : 2.19
% 7.85/2.97  Index Insertion      : 0.00
% 7.85/2.97  Index Deletion       : 0.00
% 7.85/2.97  Index Matching       : 0.00
% 7.85/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
