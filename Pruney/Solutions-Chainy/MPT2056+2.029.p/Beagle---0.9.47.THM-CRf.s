%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 285 expanded)
%              Number of leaves         :   47 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  194 ( 759 expanded)
%              Number of equality atoms :   38 ( 126 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_153,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_42,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_112,axiom,(
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

tff(f_133,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_72,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_90,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_90])).

tff(c_124,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(u1_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_124])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_127])).

tff(c_130,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_129])).

tff(c_68,plain,(
    v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_177,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_4'(A_72,B_73),A_72)
      | r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(A_74)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_211,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_187,c_34])).

tff(c_214,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_211])).

tff(c_1041,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden('#skF_2'(A_146,B_147,C_148),A_146)
      | r2_hidden('#skF_3'(A_146,B_147,C_148),C_148)
      | k4_xboole_0(A_146,B_147) = C_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_215,plain,(
    ! [B_81] : k4_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_211])).

tff(c_42,plain,(
    ! [C_24,B_23] : ~ r2_hidden(C_24,k4_xboole_0(B_23,k1_tarski(C_24))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_42])).

tff(c_1066,plain,(
    ! [B_147,C_148] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_147,C_148),C_148)
      | k4_xboole_0(k1_xboole_0,B_147) = C_148 ) ),
    inference(resolution,[status(thm)],[c_1041,c_230])).

tff(c_1124,plain,(
    ! [B_149,C_150] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_149,C_150),C_150)
      | k1_xboole_0 = C_150 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1066])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_69,B_70)),A_69)
      | v1_xboole_0(k4_xboole_0(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_192,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_417,plain,(
    ! [A_101,B_102] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_101,B_102)),B_102)
      | v1_xboole_0(k4_xboole_0(A_101,B_102)) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_439,plain,(
    ! [A_103] : v1_xboole_0(k4_xboole_0(A_103,A_103)) ),
    inference(resolution,[status(thm)],[c_164,c_417])).

tff(c_191,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = A_74
      | ~ v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_187,c_34])).

tff(c_608,plain,(
    ! [A_116,B_117] : k4_xboole_0(k4_xboole_0(A_116,A_116),B_117) = k4_xboole_0(A_116,A_116) ),
    inference(resolution,[status(thm)],[c_439,c_191])).

tff(c_661,plain,(
    ! [C_24,A_116] : ~ r2_hidden(C_24,k4_xboole_0(A_116,A_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_42])).

tff(c_1156,plain,(
    ! [A_116] : k4_xboole_0(A_116,A_116) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1124,c_661])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_270,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,B_86)
      | ~ r2_hidden(C_87,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1860,plain,(
    ! [C_184,B_185,A_186] :
      ( ~ r2_hidden(C_184,B_185)
      | ~ r2_hidden(C_184,A_186)
      | k4_xboole_0(A_186,B_185) != A_186 ) ),
    inference(resolution,[status(thm)],[c_36,c_270])).

tff(c_2093,plain,(
    ! [A_201,A_202] :
      ( ~ r2_hidden('#skF_1'(A_201),A_202)
      | k4_xboole_0(A_202,A_201) != A_202
      | v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_4,c_1860])).

tff(c_2116,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_2093])).

tff(c_2128,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_2116])).

tff(c_603,plain,(
    ! [A_112,B_113,C_114] :
      ( k7_subset_1(A_112,B_113,C_114) = k4_xboole_0(B_113,C_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_606,plain,(
    ! [C_114] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',C_114) = k4_xboole_0('#skF_6',C_114) ),
    inference(resolution,[status(thm)],[c_62,c_603])).

tff(c_2019,plain,(
    ! [A_194,B_195] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194))),B_195,k1_tarski(k1_xboole_0)) = k2_yellow19(A_194,k3_yellow19(A_194,k2_struct_0(A_194),B_195))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194)))))
      | ~ v13_waybel_0(B_195,k3_yellow_1(k2_struct_0(A_194)))
      | ~ v2_waybel_0(B_195,k3_yellow_1(k2_struct_0(A_194)))
      | v1_xboole_0(B_195)
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2021,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))),'#skF_6',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6'))
    | ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2019])).

tff(c_2024,plain,
    ( k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_64,c_606,c_2021])).

tff(c_2025,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) = k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_2024])).

tff(c_60,plain,(
    k2_yellow19('#skF_5',k3_yellow19('#skF_5',k2_struct_0('#skF_5'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2123,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2025,c_60])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(A_22,k4_xboole_0(B_23,k1_tarski(C_24)))
      | C_24 = A_22
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_718,plain,(
    ! [C_118,A_119] : ~ r2_hidden(C_118,k4_xboole_0(A_119,A_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_42])).

tff(c_842,plain,(
    ! [C_127,A_128] :
      ( C_127 = A_128
      | ~ r2_hidden(A_128,k1_tarski(C_127)) ) ),
    inference(resolution,[status(thm)],[c_40,c_718])).

tff(c_1489,plain,(
    ! [A_166,C_167] :
      ( '#skF_4'(A_166,k1_tarski(C_167)) = C_167
      | r1_xboole_0(A_166,k1_tarski(C_167)) ) ),
    inference(resolution,[status(thm)],[c_28,c_842])).

tff(c_12912,plain,(
    ! [A_470,C_471] :
      ( k4_xboole_0(A_470,k1_tarski(C_471)) = A_470
      | '#skF_4'(A_470,k1_tarski(C_471)) = C_471 ) ),
    inference(resolution,[status(thm)],[c_1489,c_34])).

tff(c_13376,plain,(
    '#skF_4'('#skF_6',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12912,c_2123])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_13398,plain,
    ( r2_hidden(k1_xboole_0,'#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13376,c_30])).

tff(c_13409,plain,(
    r1_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_13398])).

tff(c_13414,plain,(
    k4_xboole_0('#skF_6',k1_tarski(k1_xboole_0)) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13409,c_34])).

tff(c_13419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2123,c_13414])).

tff(c_13420,plain,(
    r2_hidden(k1_xboole_0,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_13398])).

tff(c_58,plain,(
    ! [C_42,B_40,A_36] :
      ( ~ v1_xboole_0(C_42)
      | ~ r2_hidden(C_42,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v2_waybel_0(B_40,k3_yellow_1(A_36))
      | ~ v1_subset_1(B_40,u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_13433,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_13420,c_58])).

tff(c_13446,plain,(
    ! [A_36] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_36))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_36)))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_13433])).

tff(c_13839,plain,(
    ! [A_477] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_477))))
      | ~ v13_waybel_0('#skF_6',k3_yellow_1(A_477))
      | ~ v2_waybel_0('#skF_6',k3_yellow_1(A_477))
      | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(A_477)))
      | v1_xboole_0(A_477) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13446])).

tff(c_13842,plain,
    ( ~ v13_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_6',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_6',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_13839])).

tff(c_13845,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_13842])).

tff(c_13847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_13845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.87  
% 7.80/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.88  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 7.80/2.88  
% 7.80/2.88  %Foreground sorts:
% 7.80/2.88  
% 7.80/2.88  
% 7.80/2.88  %Background operators:
% 7.80/2.88  
% 7.80/2.88  
% 7.80/2.88  %Foreground operators:
% 7.80/2.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.80/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.88  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 7.80/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.80/2.88  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.80/2.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.80/2.88  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 7.80/2.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.80/2.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.80/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/2.88  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 7.80/2.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.80/2.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.80/2.88  tff('#skF_5', type, '#skF_5': $i).
% 7.80/2.88  tff('#skF_6', type, '#skF_6': $i).
% 7.80/2.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.80/2.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.80/2.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.80/2.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.80/2.88  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 7.80/2.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.80/2.88  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 7.80/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.80/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.88  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 7.80/2.88  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 7.80/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.80/2.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.80/2.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.80/2.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.80/2.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.80/2.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.80/2.88  
% 7.80/2.89  tff(f_153, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 7.80/2.89  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.80/2.89  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.80/2.89  tff(f_42, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.80/2.89  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.80/2.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.80/2.89  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.80/2.89  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.80/2.89  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.80/2.89  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.80/2.89  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 7.80/2.89  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 7.80/2.89  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_72, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_90, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.80/2.89  tff(c_94, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_90])).
% 7.80/2.89  tff(c_124, plain, (![A_59]: (~v1_xboole_0(u1_struct_0(A_59)) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.80/2.89  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_94, c_124])).
% 7.80/2.89  tff(c_129, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_127])).
% 7.80/2.89  tff(c_130, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_129])).
% 7.80/2.89  tff(c_68, plain, (v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_66, plain, (v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_64, plain, (v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_70, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_24, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.80/2.89  tff(c_177, plain, (![A_72, B_73]: (r2_hidden('#skF_4'(A_72, B_73), A_72) | r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.89  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/2.89  tff(c_187, plain, (![A_74, B_75]: (~v1_xboole_0(A_74) | r1_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_177, c_2])).
% 7.80/2.89  tff(c_34, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.80/2.89  tff(c_211, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=A_79 | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_187, c_34])).
% 7.80/2.89  tff(c_214, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_211])).
% 7.80/2.89  tff(c_1041, plain, (![A_146, B_147, C_148]: (r2_hidden('#skF_2'(A_146, B_147, C_148), A_146) | r2_hidden('#skF_3'(A_146, B_147, C_148), C_148) | k4_xboole_0(A_146, B_147)=C_148)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/2.89  tff(c_215, plain, (![B_81]: (k4_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_211])).
% 7.80/2.89  tff(c_42, plain, (![C_24, B_23]: (~r2_hidden(C_24, k4_xboole_0(B_23, k1_tarski(C_24))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.80/2.89  tff(c_230, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_215, c_42])).
% 7.80/2.89  tff(c_1066, plain, (![B_147, C_148]: (r2_hidden('#skF_3'(k1_xboole_0, B_147, C_148), C_148) | k4_xboole_0(k1_xboole_0, B_147)=C_148)), inference(resolution, [status(thm)], [c_1041, c_230])).
% 7.80/2.89  tff(c_1124, plain, (![B_149, C_150]: (r2_hidden('#skF_3'(k1_xboole_0, B_149, C_150), C_150) | k1_xboole_0=C_150)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1066])).
% 7.80/2.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/2.89  tff(c_154, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k4_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/2.89  tff(c_164, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(k4_xboole_0(A_69, B_70)), A_69) | v1_xboole_0(k4_xboole_0(A_69, B_70)))), inference(resolution, [status(thm)], [c_4, c_154])).
% 7.80/2.89  tff(c_192, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k4_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/2.89  tff(c_417, plain, (![A_101, B_102]: (~r2_hidden('#skF_1'(k4_xboole_0(A_101, B_102)), B_102) | v1_xboole_0(k4_xboole_0(A_101, B_102)))), inference(resolution, [status(thm)], [c_4, c_192])).
% 7.80/2.89  tff(c_439, plain, (![A_103]: (v1_xboole_0(k4_xboole_0(A_103, A_103)))), inference(resolution, [status(thm)], [c_164, c_417])).
% 7.80/2.89  tff(c_191, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=A_74 | ~v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_187, c_34])).
% 7.80/2.89  tff(c_608, plain, (![A_116, B_117]: (k4_xboole_0(k4_xboole_0(A_116, A_116), B_117)=k4_xboole_0(A_116, A_116))), inference(resolution, [status(thm)], [c_439, c_191])).
% 7.80/2.89  tff(c_661, plain, (![C_24, A_116]: (~r2_hidden(C_24, k4_xboole_0(A_116, A_116)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_42])).
% 7.80/2.89  tff(c_1156, plain, (![A_116]: (k4_xboole_0(A_116, A_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1124, c_661])).
% 7.80/2.89  tff(c_36, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.80/2.89  tff(c_270, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, B_86) | ~r2_hidden(C_87, A_85))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.89  tff(c_1860, plain, (![C_184, B_185, A_186]: (~r2_hidden(C_184, B_185) | ~r2_hidden(C_184, A_186) | k4_xboole_0(A_186, B_185)!=A_186)), inference(resolution, [status(thm)], [c_36, c_270])).
% 7.80/2.89  tff(c_2093, plain, (![A_201, A_202]: (~r2_hidden('#skF_1'(A_201), A_202) | k4_xboole_0(A_202, A_201)!=A_202 | v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_4, c_1860])).
% 7.80/2.89  tff(c_2116, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_2093])).
% 7.80/2.89  tff(c_2128, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_2116])).
% 7.80/2.89  tff(c_603, plain, (![A_112, B_113, C_114]: (k7_subset_1(A_112, B_113, C_114)=k4_xboole_0(B_113, C_114) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.80/2.89  tff(c_606, plain, (![C_114]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', C_114)=k4_xboole_0('#skF_6', C_114))), inference(resolution, [status(thm)], [c_62, c_603])).
% 7.80/2.89  tff(c_2019, plain, (![A_194, B_195]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194))), B_195, k1_tarski(k1_xboole_0))=k2_yellow19(A_194, k3_yellow19(A_194, k2_struct_0(A_194), B_195)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_194))))) | ~v13_waybel_0(B_195, k3_yellow_1(k2_struct_0(A_194))) | ~v2_waybel_0(B_195, k3_yellow_1(k2_struct_0(A_194))) | v1_xboole_0(B_195) | ~l1_struct_0(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.80/2.89  tff(c_2021, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))), '#skF_6', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6')) | ~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2019])).
% 7.80/2.89  tff(c_2024, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_64, c_606, c_2021])).
% 7.80/2.89  tff(c_2025, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))=k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_2024])).
% 7.80/2.89  tff(c_60, plain, (k2_yellow19('#skF_5', k3_yellow19('#skF_5', k2_struct_0('#skF_5'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.80/2.89  tff(c_2123, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2025, c_60])).
% 7.80/2.89  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.89  tff(c_40, plain, (![A_22, B_23, C_24]: (r2_hidden(A_22, k4_xboole_0(B_23, k1_tarski(C_24))) | C_24=A_22 | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.80/2.89  tff(c_718, plain, (![C_118, A_119]: (~r2_hidden(C_118, k4_xboole_0(A_119, A_119)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_42])).
% 7.80/2.89  tff(c_842, plain, (![C_127, A_128]: (C_127=A_128 | ~r2_hidden(A_128, k1_tarski(C_127)))), inference(resolution, [status(thm)], [c_40, c_718])).
% 7.80/2.89  tff(c_1489, plain, (![A_166, C_167]: ('#skF_4'(A_166, k1_tarski(C_167))=C_167 | r1_xboole_0(A_166, k1_tarski(C_167)))), inference(resolution, [status(thm)], [c_28, c_842])).
% 7.80/2.89  tff(c_12912, plain, (![A_470, C_471]: (k4_xboole_0(A_470, k1_tarski(C_471))=A_470 | '#skF_4'(A_470, k1_tarski(C_471))=C_471)), inference(resolution, [status(thm)], [c_1489, c_34])).
% 7.80/2.89  tff(c_13376, plain, ('#skF_4'('#skF_6', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12912, c_2123])).
% 7.80/2.89  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.89  tff(c_13398, plain, (r2_hidden(k1_xboole_0, '#skF_6') | r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13376, c_30])).
% 7.80/2.89  tff(c_13409, plain, (r1_xboole_0('#skF_6', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_13398])).
% 7.80/2.89  tff(c_13414, plain, (k4_xboole_0('#skF_6', k1_tarski(k1_xboole_0))='#skF_6'), inference(resolution, [status(thm)], [c_13409, c_34])).
% 7.80/2.89  tff(c_13419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2123, c_13414])).
% 7.80/2.89  tff(c_13420, plain, (r2_hidden(k1_xboole_0, '#skF_6')), inference(splitRight, [status(thm)], [c_13398])).
% 7.80/2.89  tff(c_58, plain, (![C_42, B_40, A_36]: (~v1_xboole_0(C_42) | ~r2_hidden(C_42, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0(B_40, k3_yellow_1(A_36)) | ~v2_waybel_0(B_40, k3_yellow_1(A_36)) | ~v1_subset_1(B_40, u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0(B_40) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.80/2.89  tff(c_13433, plain, (![A_36]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_13420, c_58])).
% 7.80/2.89  tff(c_13446, plain, (![A_36]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_36)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_36)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_36))) | v1_xboole_0('#skF_6') | v1_xboole_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_13433])).
% 7.80/2.89  tff(c_13839, plain, (![A_477]: (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_477)))) | ~v13_waybel_0('#skF_6', k3_yellow_1(A_477)) | ~v2_waybel_0('#skF_6', k3_yellow_1(A_477)) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(A_477))) | v1_xboole_0(A_477))), inference(negUnitSimplification, [status(thm)], [c_70, c_13446])).
% 7.80/2.89  tff(c_13842, plain, (~v13_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_6', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_6', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_13839])).
% 7.80/2.89  tff(c_13845, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_13842])).
% 7.80/2.89  tff(c_13847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_13845])).
% 7.80/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.89  
% 7.80/2.89  Inference rules
% 7.80/2.89  ----------------------
% 7.80/2.89  #Ref     : 2
% 7.80/2.89  #Sup     : 3587
% 7.80/2.89  #Fact    : 0
% 7.80/2.89  #Define  : 0
% 7.80/2.89  #Split   : 2
% 7.80/2.89  #Chain   : 0
% 7.80/2.89  #Close   : 0
% 7.80/2.89  
% 7.80/2.89  Ordering : KBO
% 7.80/2.89  
% 7.80/2.89  Simplification rules
% 7.80/2.89  ----------------------
% 7.80/2.89  #Subsume      : 1303
% 7.80/2.89  #Demod        : 1486
% 7.80/2.89  #Tautology    : 1241
% 7.80/2.89  #SimpNegUnit  : 42
% 7.80/2.89  #BackRed      : 8
% 7.80/2.89  
% 7.80/2.89  #Partial instantiations: 0
% 7.80/2.89  #Strategies tried      : 1
% 7.80/2.89  
% 7.80/2.89  Timing (in seconds)
% 7.80/2.89  ----------------------
% 7.80/2.90  Preprocessing        : 0.37
% 7.80/2.90  Parsing              : 0.19
% 7.80/2.90  CNF conversion       : 0.03
% 7.80/2.90  Main loop            : 1.71
% 7.80/2.90  Inferencing          : 0.49
% 7.80/2.90  Reduction            : 0.61
% 7.80/2.90  Demodulation         : 0.46
% 7.80/2.90  BG Simplification    : 0.06
% 7.80/2.90  Subsumption          : 0.43
% 7.80/2.90  Abstraction          : 0.09
% 7.80/2.90  MUC search           : 0.00
% 7.80/2.90  Cooper               : 0.00
% 7.80/2.90  Total                : 2.11
% 7.80/2.90  Index Insertion      : 0.00
% 7.80/2.90  Index Deletion       : 0.00
% 7.80/2.90  Index Matching       : 0.00
% 7.80/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
