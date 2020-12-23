%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   62 (  83 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 221 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_105,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
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

tff(f_85,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,k1_tarski(B_4)) = A_3
      | r2_hidden(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_29,B_30,C_31] :
      ( k7_subset_1(A_29,B_30,C_31) = k4_xboole_0(B_30,C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [C_31] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_31) = k4_xboole_0('#skF_2',C_31) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_82,plain,(
    ! [A_36,B_37] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))),B_37,k1_tarski(k1_xboole_0)) = k2_yellow19(A_36,k3_yellow19(A_36,k2_struct_0(A_36),B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36)))))
      | ~ v13_waybel_0(B_37,k3_yellow_1(k2_struct_0(A_36)))
      | ~ v2_waybel_0(B_37,k3_yellow_1(k2_struct_0(A_36)))
      | v1_xboole_0(B_37)
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_87,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_24,c_71,c_84])).

tff(c_88,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_30,c_87])).

tff(c_20,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_89,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20])).

tff(c_97,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_18,plain,(
    ! [C_19,B_17,A_13] :
      ( ~ v1_xboole_0(C_19)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13))))
      | ~ v13_waybel_0(B_17,k3_yellow_1(A_13))
      | ~ v2_waybel_0(B_17,k3_yellow_1(A_13))
      | ~ v1_subset_1(B_17,u1_struct_0(k3_yellow_1(A_13)))
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_13))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_13))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_13)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_13) ) ),
    inference(resolution,[status(thm)],[c_97,c_18])).

tff(c_102,plain,(
    ! [A_13] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_13))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_13))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_13)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_104,plain,(
    ! [A_38] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_38))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_38))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_38))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_38)))
      | v1_xboole_0(A_38) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_102])).

tff(c_107,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_110,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_107])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_12])).

tff(c_116,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.22  
% 2.15/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.23  
% 2.15/1.23  %Foreground sorts:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Background operators:
% 2.15/1.23  
% 2.15/1.23  
% 2.15/1.23  %Foreground operators:
% 2.15/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.23  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.15/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.15/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.23  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.15/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.23  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.15/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.23  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.15/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.23  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.15/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.15/1.23  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.23  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.15/1.23  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.15/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.15/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.23  
% 2.29/1.24  tff(f_105, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.29/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.29/1.24  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.29/1.24  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.29/1.24  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.29/1.24  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.29/1.24  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.29/1.24  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_32, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_28, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_26, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_24, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_30, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.29/1.24  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k1_tarski(B_4))=A_3 | r2_hidden(B_4, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.24  tff(c_68, plain, (![A_29, B_30, C_31]: (k7_subset_1(A_29, B_30, C_31)=k4_xboole_0(B_30, C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.24  tff(c_71, plain, (![C_31]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_31)=k4_xboole_0('#skF_2', C_31))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.29/1.24  tff(c_82, plain, (![A_36, B_37]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))), B_37, k1_tarski(k1_xboole_0))=k2_yellow19(A_36, k3_yellow19(A_36, k2_struct_0(A_36), B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_36))))) | ~v13_waybel_0(B_37, k3_yellow_1(k2_struct_0(A_36))) | ~v2_waybel_0(B_37, k3_yellow_1(k2_struct_0(A_36))) | v1_xboole_0(B_37) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.24  tff(c_84, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_82])).
% 2.29/1.24  tff(c_87, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_24, c_71, c_84])).
% 2.29/1.24  tff(c_88, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_34, c_30, c_87])).
% 2.29/1.24  tff(c_20, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.29/1.24  tff(c_89, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_20])).
% 2.29/1.24  tff(c_97, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 2.29/1.24  tff(c_18, plain, (![C_19, B_17, A_13]: (~v1_xboole_0(C_19) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13)))) | ~v13_waybel_0(B_17, k3_yellow_1(A_13)) | ~v2_waybel_0(B_17, k3_yellow_1(A_13)) | ~v1_subset_1(B_17, u1_struct_0(k3_yellow_1(A_13))) | v1_xboole_0(B_17) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.24  tff(c_99, plain, (![A_13]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_13)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_13)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_13))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_97, c_18])).
% 2.29/1.24  tff(c_102, plain, (![A_13]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_13)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_13)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_13)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_13))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 2.29/1.24  tff(c_104, plain, (![A_38]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_38)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_38)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_38)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_38))) | v1_xboole_0(A_38))), inference(negUnitSimplification, [status(thm)], [c_30, c_102])).
% 2.29/1.24  tff(c_107, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_104])).
% 2.29/1.24  tff(c_110, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_107])).
% 2.29/1.24  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k2_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.24  tff(c_113, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_110, c_12])).
% 2.29/1.24  tff(c_116, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113])).
% 2.29/1.24  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_116])).
% 2.29/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.24  
% 2.29/1.24  Inference rules
% 2.29/1.24  ----------------------
% 2.29/1.24  #Ref     : 0
% 2.29/1.24  #Sup     : 17
% 2.29/1.24  #Fact    : 0
% 2.29/1.24  #Define  : 0
% 2.29/1.24  #Split   : 0
% 2.29/1.24  #Chain   : 0
% 2.29/1.24  #Close   : 0
% 2.29/1.24  
% 2.29/1.24  Ordering : KBO
% 2.29/1.24  
% 2.29/1.24  Simplification rules
% 2.29/1.24  ----------------------
% 2.29/1.24  #Subsume      : 0
% 2.29/1.24  #Demod        : 10
% 2.29/1.24  #Tautology    : 11
% 2.29/1.24  #SimpNegUnit  : 3
% 2.29/1.24  #BackRed      : 1
% 2.29/1.24  
% 2.29/1.24  #Partial instantiations: 0
% 2.29/1.24  #Strategies tried      : 1
% 2.29/1.24  
% 2.29/1.24  Timing (in seconds)
% 2.29/1.24  ----------------------
% 2.29/1.24  Preprocessing        : 0.32
% 2.29/1.24  Parsing              : 0.17
% 2.29/1.24  CNF conversion       : 0.02
% 2.29/1.24  Main loop            : 0.13
% 2.29/1.24  Inferencing          : 0.05
% 2.29/1.24  Reduction            : 0.04
% 2.29/1.24  Demodulation         : 0.03
% 2.29/1.24  BG Simplification    : 0.01
% 2.29/1.24  Subsumption          : 0.01
% 2.29/1.24  Abstraction          : 0.01
% 2.29/1.24  MUC search           : 0.00
% 2.29/1.24  Cooper               : 0.00
% 2.29/1.24  Total                : 0.47
% 2.29/1.24  Index Insertion      : 0.00
% 2.29/1.24  Index Deletion       : 0.00
% 2.29/1.24  Index Matching       : 0.00
% 2.29/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
