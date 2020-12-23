%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 233 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
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

tff(f_91,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_49,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_65,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,k1_tarski(A_34))
      | r2_hidden(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [B_33,A_34] :
      ( k4_xboole_0(B_33,k1_tarski(A_34)) = B_33
      | r2_hidden(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_65,c_6])).

tff(c_94,plain,(
    ! [A_41,B_42,C_43] :
      ( k7_subset_1(A_41,B_42,C_43) = k4_xboole_0(B_42,C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [C_43] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_43) = k4_xboole_0('#skF_2',C_43) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_130,plain,(
    ! [A_50,B_51] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_50))),B_51,k1_tarski(k1_xboole_0)) = k2_yellow19(A_50,k3_yellow19(A_50,k2_struct_0(A_50),B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_50)))))
      | ~ v13_waybel_0(B_51,k3_yellow_1(k2_struct_0(A_50)))
      | ~ v2_waybel_0(B_51,k3_yellow_1(k2_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_132,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_135,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_26,c_97,c_132])).

tff(c_136,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_135])).

tff(c_22,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_137,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_22])).

tff(c_145,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_137])).

tff(c_20,plain,(
    ! [C_21,B_19,A_15] :
      ( ~ v1_xboole_0(C_21)
      | ~ r2_hidden(C_21,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15))))
      | ~ v13_waybel_0(B_19,k3_yellow_1(A_15))
      | ~ v2_waybel_0(B_19,k3_yellow_1(A_15))
      | ~ v1_subset_1(B_19,u1_struct_0(k3_yellow_1(A_15)))
      | v1_xboole_0(B_19)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_147,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_15))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_15))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_15)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_145,c_20])).

tff(c_150,plain,(
    ! [A_15] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_15))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_15))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_15)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_152,plain,(
    ! [A_52] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_52))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_52))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_52))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_52)))
      | v1_xboole_0(A_52) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_150])).

tff(c_155,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_152])).

tff(c_158,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_155])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_161,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_14])).

tff(c_164,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_161])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.16/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.30  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.16/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.30  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.16/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.30  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.16/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.30  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.16/1.30  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.16/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.16/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.30  
% 2.16/1.31  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.16/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.31  tff(f_39, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.16/1.31  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.16/1.31  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.16/1.31  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.16/1.31  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.16/1.31  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.16/1.31  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.16/1.31  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_34, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_30, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_28, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_26, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.16/1.31  tff(c_49, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.31  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.16/1.31  tff(c_65, plain, (![B_33, A_34]: (r1_xboole_0(B_33, k1_tarski(A_34)) | r2_hidden(A_34, B_33))), inference(resolution, [status(thm)], [c_49, c_4])).
% 2.16/1.31  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.31  tff(c_71, plain, (![B_33, A_34]: (k4_xboole_0(B_33, k1_tarski(A_34))=B_33 | r2_hidden(A_34, B_33))), inference(resolution, [status(thm)], [c_65, c_6])).
% 2.16/1.31  tff(c_94, plain, (![A_41, B_42, C_43]: (k7_subset_1(A_41, B_42, C_43)=k4_xboole_0(B_42, C_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.31  tff(c_97, plain, (![C_43]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_43)=k4_xboole_0('#skF_2', C_43))), inference(resolution, [status(thm)], [c_24, c_94])).
% 2.16/1.31  tff(c_130, plain, (![A_50, B_51]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_50))), B_51, k1_tarski(k1_xboole_0))=k2_yellow19(A_50, k3_yellow19(A_50, k2_struct_0(A_50), B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_50))))) | ~v13_waybel_0(B_51, k3_yellow_1(k2_struct_0(A_50))) | ~v2_waybel_0(B_51, k3_yellow_1(k2_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.31  tff(c_132, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_130])).
% 2.16/1.31  tff(c_135, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_26, c_97, c_132])).
% 2.16/1.31  tff(c_136, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_135])).
% 2.16/1.31  tff(c_22, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.31  tff(c_137, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_22])).
% 2.16/1.31  tff(c_145, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_137])).
% 2.16/1.31  tff(c_20, plain, (![C_21, B_19, A_15]: (~v1_xboole_0(C_21) | ~r2_hidden(C_21, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15)))) | ~v13_waybel_0(B_19, k3_yellow_1(A_15)) | ~v2_waybel_0(B_19, k3_yellow_1(A_15)) | ~v1_subset_1(B_19, u1_struct_0(k3_yellow_1(A_15))) | v1_xboole_0(B_19) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.31  tff(c_147, plain, (![A_15]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_15)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_15)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_15))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_145, c_20])).
% 2.16/1.31  tff(c_150, plain, (![A_15]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_15)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_15)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_15)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_15))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_147])).
% 2.16/1.31  tff(c_152, plain, (![A_52]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_52)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_52)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_52)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_52))) | v1_xboole_0(A_52))), inference(negUnitSimplification, [status(thm)], [c_32, c_150])).
% 2.16/1.31  tff(c_155, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_152])).
% 2.16/1.31  tff(c_158, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_155])).
% 2.16/1.31  tff(c_14, plain, (![A_10]: (~v1_xboole_0(k2_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.31  tff(c_161, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_158, c_14])).
% 2.16/1.31  tff(c_164, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_161])).
% 2.16/1.31  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_164])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 28
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 0
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 4
% 2.16/1.31  #Demod        : 10
% 2.16/1.31  #Tautology    : 13
% 2.16/1.31  #SimpNegUnit  : 3
% 2.16/1.31  #BackRed      : 1
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.31  Preprocessing        : 0.32
% 2.16/1.31  Parsing              : 0.18
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.15
% 2.16/1.31  Inferencing          : 0.06
% 2.16/1.31  Reduction            : 0.05
% 2.16/1.31  Demodulation         : 0.03
% 2.16/1.31  BG Simplification    : 0.01
% 2.16/1.31  Subsumption          : 0.02
% 2.16/1.31  Abstraction          : 0.01
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.51
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
