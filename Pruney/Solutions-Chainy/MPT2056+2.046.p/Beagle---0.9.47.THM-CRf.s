%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:31 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 105 expanded)
%              Number of leaves         :   40 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 252 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_135,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_135])).

tff(c_150,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_111,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,k1_tarski(A_45))
      | r2_hidden(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_111,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_217,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(B_57,k1_tarski(A_58)) = k1_xboole_0
      | r2_hidden(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_229,plain,(
    ! [B_57,A_58] :
      ( k4_xboole_0(B_57,k1_tarski(A_58)) = k5_xboole_0(B_57,k1_xboole_0)
      | r2_hidden(A_58,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_248,plain,(
    ! [B_57,A_58] :
      ( k4_xboole_0(B_57,k1_tarski(A_58)) = B_57
      | r2_hidden(A_58,B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_229])).

tff(c_178,plain,(
    ! [A_50,B_51,C_52] :
      ( k7_subset_1(A_50,B_51,C_52) = k4_xboole_0(B_51,C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_181,plain,(
    ! [C_52] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_52) = k4_xboole_0('#skF_2',C_52) ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_311,plain,(
    ! [A_67,B_68] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))),B_68,k1_tarski(k1_xboole_0)) = k2_yellow19(A_67,k3_yellow19(A_67,k2_struct_0(A_67),B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67)))))
      | ~ v13_waybel_0(B_68,k3_yellow_1(k2_struct_0(A_67)))
      | ~ v2_waybel_0(B_68,k3_yellow_1(k2_struct_0(A_67)))
      | v1_xboole_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_313,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_311])).

tff(c_316,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_32,c_181,c_313])).

tff(c_317,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_316])).

tff(c_28,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_318,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_28])).

tff(c_326,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_318])).

tff(c_26,plain,(
    ! [C_25,B_23,A_19] :
      ( ~ v1_xboole_0(C_25)
      | ~ r2_hidden(C_25,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19))))
      | ~ v13_waybel_0(B_23,k3_yellow_1(A_19))
      | ~ v2_waybel_0(B_23,k3_yellow_1(A_19))
      | ~ v1_subset_1(B_23,u1_struct_0(k3_yellow_1(A_19)))
      | v1_xboole_0(B_23)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_328,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_19))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_19))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_19)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_326,c_26])).

tff(c_331,plain,(
    ! [A_19] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_19))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_19))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_19)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_328])).

tff(c_333,plain,(
    ! [A_69] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_69))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_69))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_69))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_69)))
      | v1_xboole_0(A_69) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_331])).

tff(c_336,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_333])).

tff(c_339,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_336])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k2_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_342,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_339,c_20])).

tff(c_345,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_342])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.38  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1
% 2.32/1.38  
% 2.32/1.38  %Foreground sorts:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Background operators:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Foreground operators:
% 2.32/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.38  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.32/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.32/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.38  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.32/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.38  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.32/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.32/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.32/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.38  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.32/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.38  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.38  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.32/1.38  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.32/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.32/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.38  
% 2.32/1.39  tff(f_117, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.32/1.39  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.32/1.39  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.32/1.39  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.32/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.32/1.39  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.32/1.39  tff(f_45, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.32/1.39  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.32/1.39  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.32/1.39  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.32/1.39  tff(f_97, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.32/1.39  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.32/1.39  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_40, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_36, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_34, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_32, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.32/1.39  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.32/1.39  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.32/1.39  tff(c_75, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.39  tff(c_87, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_75])).
% 2.32/1.39  tff(c_135, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.39  tff(c_147, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_87, c_135])).
% 2.32/1.39  tff(c_150, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_147])).
% 2.32/1.39  tff(c_111, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.39  tff(c_8, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.32/1.39  tff(c_127, plain, (![B_44, A_45]: (r1_xboole_0(B_44, k1_tarski(A_45)) | r2_hidden(A_45, B_44))), inference(resolution, [status(thm)], [c_111, c_8])).
% 2.32/1.39  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.39  tff(c_217, plain, (![B_57, A_58]: (k3_xboole_0(B_57, k1_tarski(A_58))=k1_xboole_0 | r2_hidden(A_58, B_57))), inference(resolution, [status(thm)], [c_127, c_2])).
% 2.32/1.39  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.32/1.39  tff(c_229, plain, (![B_57, A_58]: (k4_xboole_0(B_57, k1_tarski(A_58))=k5_xboole_0(B_57, k1_xboole_0) | r2_hidden(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 2.32/1.39  tff(c_248, plain, (![B_57, A_58]: (k4_xboole_0(B_57, k1_tarski(A_58))=B_57 | r2_hidden(A_58, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_229])).
% 2.32/1.39  tff(c_178, plain, (![A_50, B_51, C_52]: (k7_subset_1(A_50, B_51, C_52)=k4_xboole_0(B_51, C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.39  tff(c_181, plain, (![C_52]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_52)=k4_xboole_0('#skF_2', C_52))), inference(resolution, [status(thm)], [c_30, c_178])).
% 2.32/1.39  tff(c_311, plain, (![A_67, B_68]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))), B_68, k1_tarski(k1_xboole_0))=k2_yellow19(A_67, k3_yellow19(A_67, k2_struct_0(A_67), B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_67))))) | ~v13_waybel_0(B_68, k3_yellow_1(k2_struct_0(A_67))) | ~v2_waybel_0(B_68, k3_yellow_1(k2_struct_0(A_67))) | v1_xboole_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.32/1.39  tff(c_313, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_311])).
% 2.32/1.39  tff(c_316, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_32, c_181, c_313])).
% 2.32/1.39  tff(c_317, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_316])).
% 2.32/1.39  tff(c_28, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.32/1.39  tff(c_318, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_317, c_28])).
% 2.32/1.39  tff(c_326, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_318])).
% 2.32/1.39  tff(c_26, plain, (![C_25, B_23, A_19]: (~v1_xboole_0(C_25) | ~r2_hidden(C_25, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19)))) | ~v13_waybel_0(B_23, k3_yellow_1(A_19)) | ~v2_waybel_0(B_23, k3_yellow_1(A_19)) | ~v1_subset_1(B_23, u1_struct_0(k3_yellow_1(A_19))) | v1_xboole_0(B_23) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.32/1.39  tff(c_328, plain, (![A_19]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_19)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_19)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_19))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_326, c_26])).
% 2.32/1.39  tff(c_331, plain, (![A_19]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_19)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_19)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_19)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_19))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_328])).
% 2.32/1.39  tff(c_333, plain, (![A_69]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_69)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_69)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_69)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_69))) | v1_xboole_0(A_69))), inference(negUnitSimplification, [status(thm)], [c_38, c_331])).
% 2.32/1.39  tff(c_336, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_333])).
% 2.32/1.39  tff(c_339, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_336])).
% 2.32/1.39  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k2_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.39  tff(c_342, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_339, c_20])).
% 2.32/1.39  tff(c_345, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_342])).
% 2.32/1.39  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_345])).
% 2.32/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.39  
% 2.32/1.39  Inference rules
% 2.32/1.39  ----------------------
% 2.32/1.39  #Ref     : 0
% 2.32/1.39  #Sup     : 68
% 2.32/1.39  #Fact    : 0
% 2.32/1.39  #Define  : 0
% 2.32/1.39  #Split   : 0
% 2.32/1.39  #Chain   : 0
% 2.32/1.39  #Close   : 0
% 2.32/1.39  
% 2.32/1.39  Ordering : KBO
% 2.32/1.39  
% 2.32/1.39  Simplification rules
% 2.32/1.39  ----------------------
% 2.32/1.39  #Subsume      : 4
% 2.32/1.39  #Demod        : 17
% 2.32/1.39  #Tautology    : 46
% 2.32/1.39  #SimpNegUnit  : 3
% 2.32/1.39  #BackRed      : 1
% 2.32/1.39  
% 2.32/1.39  #Partial instantiations: 0
% 2.32/1.39  #Strategies tried      : 1
% 2.32/1.39  
% 2.32/1.39  Timing (in seconds)
% 2.32/1.39  ----------------------
% 2.32/1.40  Preprocessing        : 0.33
% 2.32/1.40  Parsing              : 0.18
% 2.32/1.40  CNF conversion       : 0.02
% 2.32/1.40  Main loop            : 0.21
% 2.32/1.40  Inferencing          : 0.09
% 2.32/1.40  Reduction            : 0.07
% 2.32/1.40  Demodulation         : 0.05
% 2.32/1.40  BG Simplification    : 0.01
% 2.32/1.40  Subsumption          : 0.03
% 2.32/1.40  Abstraction          : 0.01
% 2.32/1.40  MUC search           : 0.00
% 2.32/1.40  Cooper               : 0.00
% 2.32/1.40  Total                : 0.58
% 2.32/1.40  Index Insertion      : 0.00
% 2.32/1.40  Index Deletion       : 0.00
% 2.32/1.40  Index Matching       : 0.00
% 2.32/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
