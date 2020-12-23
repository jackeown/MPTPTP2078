%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:25 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 164 expanded)
%              Number of leaves         :   53 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 343 expanded)
%              Number of equality atoms :   39 (  83 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k4_mcart_1 > k2_enumset1 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_88,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_104,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_52,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_175,plain,(
    ! [A_74] :
      ( u1_struct_0(A_74) = k2_struct_0(A_74)
      | ~ l1_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_179,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_175])).

tff(c_220,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(u1_struct_0(A_80))
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_223,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_220])).

tff(c_228,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_223])).

tff(c_229,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_228])).

tff(c_38,plain,(
    ! [A_46] : k9_setfam_1(A_46) = k1_zfmisc_1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_50] : u1_struct_0(k3_yellow_1(A_50)) = k9_setfam_1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_67,plain,(
    v1_subset_1('#skF_5',k9_setfam_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_72,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_67])).

tff(c_58,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_54])).

tff(c_73,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_184,plain,(
    ! [A_75,B_76] : k1_setfam_1(k2_tarski(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_239,plain,(
    ! [B_83,A_84] : k1_setfam_1(k2_tarski(B_83,A_84)) = k3_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_30,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_245,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_30])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_317,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,k3_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_337,plain,(
    ! [A_92,B_93] :
      ( ~ r1_xboole_0(A_92,B_93)
      | k3_xboole_0(A_92,B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_317])).

tff(c_481,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(k1_tarski(A_119),B_120) = k1_xboole_0
      | r2_hidden(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_24,c_337])).

tff(c_635,plain,(
    ! [A_134,A_135] :
      ( k3_xboole_0(A_134,k1_tarski(A_135)) = k1_xboole_0
      | r2_hidden(A_135,A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_481])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_675,plain,(
    ! [A_134,A_135] :
      ( k4_xboole_0(A_134,k1_tarski(A_135)) = k5_xboole_0(A_134,k1_xboole_0)
      | r2_hidden(A_135,A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_12])).

tff(c_708,plain,(
    ! [A_134,A_135] :
      ( k4_xboole_0(A_134,k1_tarski(A_135)) = A_134
      | r2_hidden(A_135,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_675])).

tff(c_445,plain,(
    ! [A_111,B_112,C_113] :
      ( k7_subset_1(A_111,B_112,C_113) = k4_xboole_0(B_112,C_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_450,plain,(
    ! [C_113] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',C_113) = k4_xboole_0('#skF_5',C_113) ),
    inference(resolution,[status(thm)],[c_73,c_445])).

tff(c_48,plain,(
    ! [A_51,B_53] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_51))),B_53,k1_tarski(k1_xboole_0)) = k2_yellow19(A_51,k3_yellow19(A_51,k2_struct_0(A_51),B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_51)))))
      | ~ v13_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_51)))
      | ~ v2_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_51)))
      | v1_xboole_0(B_53)
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    ! [A_51,B_53] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_51)),B_53,k1_tarski(k1_xboole_0)) = k2_yellow19(A_51,k3_yellow19(A_51,k2_struct_0(A_51),B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_51))))
      | ~ v13_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_51)))
      | ~ v2_waybel_0(B_53,k3_yellow_1(k2_struct_0(A_51)))
      | v1_xboole_0(B_53)
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_48])).

tff(c_851,plain,(
    ! [A_153,B_154] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_153)),B_154,k1_tarski(k1_xboole_0)) = k2_yellow19(A_153,k3_yellow19(A_153,k2_struct_0(A_153),B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_153))))
      | ~ v13_waybel_0(B_154,k3_yellow_1(k2_struct_0(A_153)))
      | ~ v2_waybel_0(B_154,k3_yellow_1(k2_struct_0(A_153)))
      | v1_xboole_0(B_154)
      | ~ l1_struct_0(A_153)
      | v2_struct_0(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_70])).

tff(c_853,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_851])).

tff(c_856,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_56,c_450,c_853])).

tff(c_857,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_856])).

tff(c_52,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_887,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_52])).

tff(c_895,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_887])).

tff(c_50,plain,(
    ! [C_60,B_58,A_54] :
      ( ~ v1_xboole_0(C_60)
      | ~ r2_hidden(C_60,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_54))))
      | ~ v13_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v2_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v1_subset_1(B_58,u1_struct_0(k3_yellow_1(A_54)))
      | v1_xboole_0(B_58)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_69,plain,(
    ! [C_60,B_58,A_54] :
      ( ~ v1_xboole_0(C_60)
      | ~ r2_hidden(C_60,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k9_setfam_1(A_54)))
      | ~ v13_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v2_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v1_subset_1(B_58,k9_setfam_1(A_54))
      | v1_xboole_0(B_58)
      | v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_50])).

tff(c_74,plain,(
    ! [C_60,B_58,A_54] :
      ( ~ v1_xboole_0(C_60)
      | ~ r2_hidden(C_60,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ v13_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v2_waybel_0(B_58,k3_yellow_1(A_54))
      | ~ v1_subset_1(B_58,k1_zfmisc_1(A_54))
      | v1_xboole_0(B_58)
      | v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_69])).

tff(c_897,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_54))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_54))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_54))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_895,c_74])).

tff(c_907,plain,(
    ! [A_54] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_54))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_54))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_54))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_897])).

tff(c_932,plain,(
    ! [A_165] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_165)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_165))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_165))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_165))
      | v1_xboole_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_907])).

tff(c_935,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_73,c_932])).

tff(c_941,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58,c_56,c_935])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k4_mcart_1 > k2_enumset1 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.91/1.43  
% 2.91/1.43  %Foreground sorts:
% 2.91/1.43  
% 2.91/1.43  
% 2.91/1.43  %Background operators:
% 2.91/1.43  
% 2.91/1.43  
% 2.91/1.43  %Foreground operators:
% 2.91/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.43  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.91/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.91/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.43  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.91/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.91/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.43  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.91/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.43  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.91/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.91/1.43  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.91/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.91/1.43  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.91/1.43  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.91/1.43  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.91/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.91/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.43  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.91/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.91/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.91/1.43  
% 3.21/1.45  tff(f_162, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.21/1.45  tff(f_92, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.21/1.45  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.21/1.45  tff(f_88, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.21/1.45  tff(f_104, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 3.21/1.45  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.21/1.45  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.21/1.45  tff(f_52, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.21/1.45  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.21/1.45  tff(f_63, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.21/1.45  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.21/1.45  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.21/1.45  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.21/1.45  tff(f_121, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.21/1.45  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.21/1.45  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_64, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_175, plain, (![A_74]: (u1_struct_0(A_74)=k2_struct_0(A_74) | ~l1_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.21/1.45  tff(c_179, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_175])).
% 3.21/1.45  tff(c_220, plain, (![A_80]: (~v1_xboole_0(u1_struct_0(A_80)) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.45  tff(c_223, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_179, c_220])).
% 3.21/1.45  tff(c_228, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_223])).
% 3.21/1.45  tff(c_229, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_228])).
% 3.21/1.45  tff(c_38, plain, (![A_46]: (k9_setfam_1(A_46)=k1_zfmisc_1(A_46))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.45  tff(c_46, plain, (![A_50]: (u1_struct_0(k3_yellow_1(A_50))=k9_setfam_1(A_50))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.45  tff(c_60, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_67, plain, (v1_subset_1('#skF_5', k9_setfam_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 3.21/1.45  tff(c_72, plain, (v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_67])).
% 3.21/1.45  tff(c_58, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_56, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_54])).
% 3.21/1.45  tff(c_73, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68])).
% 3.21/1.45  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.45  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.45  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.21/1.45  tff(c_184, plain, (![A_75, B_76]: (k1_setfam_1(k2_tarski(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.45  tff(c_239, plain, (![B_83, A_84]: (k1_setfam_1(k2_tarski(B_83, A_84))=k3_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_16, c_184])).
% 3.21/1.45  tff(c_30, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.45  tff(c_245, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_239, c_30])).
% 3.21/1.45  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.45  tff(c_32, plain, (![A_28]: (r2_hidden('#skF_3'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.21/1.45  tff(c_317, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, k3_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.45  tff(c_337, plain, (![A_92, B_93]: (~r1_xboole_0(A_92, B_93) | k3_xboole_0(A_92, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_317])).
% 3.21/1.45  tff(c_481, plain, (![A_119, B_120]: (k3_xboole_0(k1_tarski(A_119), B_120)=k1_xboole_0 | r2_hidden(A_119, B_120))), inference(resolution, [status(thm)], [c_24, c_337])).
% 3.21/1.45  tff(c_635, plain, (![A_134, A_135]: (k3_xboole_0(A_134, k1_tarski(A_135))=k1_xboole_0 | r2_hidden(A_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_245, c_481])).
% 3.21/1.45  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.21/1.45  tff(c_675, plain, (![A_134, A_135]: (k4_xboole_0(A_134, k1_tarski(A_135))=k5_xboole_0(A_134, k1_xboole_0) | r2_hidden(A_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_635, c_12])).
% 3.21/1.45  tff(c_708, plain, (![A_134, A_135]: (k4_xboole_0(A_134, k1_tarski(A_135))=A_134 | r2_hidden(A_135, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_675])).
% 3.21/1.45  tff(c_445, plain, (![A_111, B_112, C_113]: (k7_subset_1(A_111, B_112, C_113)=k4_xboole_0(B_112, C_113) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.45  tff(c_450, plain, (![C_113]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', C_113)=k4_xboole_0('#skF_5', C_113))), inference(resolution, [status(thm)], [c_73, c_445])).
% 3.21/1.45  tff(c_48, plain, (![A_51, B_53]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_51))), B_53, k1_tarski(k1_xboole_0))=k2_yellow19(A_51, k3_yellow19(A_51, k2_struct_0(A_51), B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_51))))) | ~v13_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_51))) | ~v2_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_51))) | v1_xboole_0(B_53) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.45  tff(c_70, plain, (![A_51, B_53]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_51)), B_53, k1_tarski(k1_xboole_0))=k2_yellow19(A_51, k3_yellow19(A_51, k2_struct_0(A_51), B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_51)))) | ~v13_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_51))) | ~v2_waybel_0(B_53, k3_yellow_1(k2_struct_0(A_51))) | v1_xboole_0(B_53) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_48])).
% 3.21/1.45  tff(c_851, plain, (![A_153, B_154]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_153)), B_154, k1_tarski(k1_xboole_0))=k2_yellow19(A_153, k3_yellow19(A_153, k2_struct_0(A_153), B_154)) | ~m1_subset_1(B_154, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_153)))) | ~v13_waybel_0(B_154, k3_yellow_1(k2_struct_0(A_153))) | ~v2_waybel_0(B_154, k3_yellow_1(k2_struct_0(A_153))) | v1_xboole_0(B_154) | ~l1_struct_0(A_153) | v2_struct_0(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_70])).
% 3.21/1.45  tff(c_853, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_73, c_851])).
% 3.21/1.45  tff(c_856, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_56, c_450, c_853])).
% 3.21/1.45  tff(c_857, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_856])).
% 3.21/1.45  tff(c_52, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.21/1.45  tff(c_887, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_857, c_52])).
% 3.21/1.45  tff(c_895, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_708, c_887])).
% 3.21/1.45  tff(c_50, plain, (![C_60, B_58, A_54]: (~v1_xboole_0(C_60) | ~r2_hidden(C_60, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_54)))) | ~v13_waybel_0(B_58, k3_yellow_1(A_54)) | ~v2_waybel_0(B_58, k3_yellow_1(A_54)) | ~v1_subset_1(B_58, u1_struct_0(k3_yellow_1(A_54))) | v1_xboole_0(B_58) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.21/1.45  tff(c_69, plain, (![C_60, B_58, A_54]: (~v1_xboole_0(C_60) | ~r2_hidden(C_60, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k9_setfam_1(A_54))) | ~v13_waybel_0(B_58, k3_yellow_1(A_54)) | ~v2_waybel_0(B_58, k3_yellow_1(A_54)) | ~v1_subset_1(B_58, k9_setfam_1(A_54)) | v1_xboole_0(B_58) | v1_xboole_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_50])).
% 3.21/1.45  tff(c_74, plain, (![C_60, B_58, A_54]: (~v1_xboole_0(C_60) | ~r2_hidden(C_60, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~v13_waybel_0(B_58, k3_yellow_1(A_54)) | ~v2_waybel_0(B_58, k3_yellow_1(A_54)) | ~v1_subset_1(B_58, k1_zfmisc_1(A_54)) | v1_xboole_0(B_58) | v1_xboole_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_69])).
% 3.21/1.45  tff(c_897, plain, (![A_54]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_54)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_54)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_54)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_895, c_74])).
% 3.21/1.45  tff(c_907, plain, (![A_54]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_54)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_54)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_54)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_897])).
% 3.21/1.45  tff(c_932, plain, (![A_165]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_165))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_165)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_165)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_165)) | v1_xboole_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_62, c_907])).
% 3.21/1.45  tff(c_935, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_73, c_932])).
% 3.21/1.45  tff(c_941, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_58, c_56, c_935])).
% 3.21/1.45  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_941])).
% 3.21/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.45  
% 3.21/1.45  Inference rules
% 3.21/1.45  ----------------------
% 3.21/1.45  #Ref     : 0
% 3.21/1.45  #Sup     : 216
% 3.21/1.45  #Fact    : 0
% 3.21/1.45  #Define  : 0
% 3.21/1.45  #Split   : 1
% 3.21/1.45  #Chain   : 0
% 3.21/1.45  #Close   : 0
% 3.21/1.45  
% 3.21/1.45  Ordering : KBO
% 3.21/1.45  
% 3.21/1.45  Simplification rules
% 3.21/1.45  ----------------------
% 3.21/1.45  #Subsume      : 56
% 3.21/1.45  #Demod        : 53
% 3.21/1.45  #Tautology    : 93
% 3.21/1.45  #SimpNegUnit  : 4
% 3.21/1.45  #BackRed      : 1
% 3.21/1.45  
% 3.21/1.45  #Partial instantiations: 0
% 3.21/1.45  #Strategies tried      : 1
% 3.21/1.45  
% 3.21/1.45  Timing (in seconds)
% 3.21/1.45  ----------------------
% 3.21/1.45  Preprocessing        : 0.34
% 3.21/1.45  Parsing              : 0.18
% 3.21/1.45  CNF conversion       : 0.02
% 3.21/1.45  Main loop            : 0.35
% 3.21/1.45  Inferencing          : 0.13
% 3.21/1.45  Reduction            : 0.12
% 3.21/1.45  Demodulation         : 0.09
% 3.21/1.45  BG Simplification    : 0.02
% 3.21/1.45  Subsumption          : 0.05
% 3.21/1.45  Abstraction          : 0.02
% 3.21/1.45  MUC search           : 0.00
% 3.21/1.45  Cooper               : 0.00
% 3.21/1.45  Total                : 0.72
% 3.21/1.45  Index Insertion      : 0.00
% 3.21/1.45  Index Deletion       : 0.00
% 3.21/1.45  Index Matching       : 0.00
% 3.21/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
