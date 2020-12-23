%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:32 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 238 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
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

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_33,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_42,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_42])).

tff(c_47,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_45])).

tff(c_48,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_47])).

tff(c_26,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,k1_tarski(B_2)) = A_1
      | r2_hidden(B_2,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_25,B_26,C_27] :
      ( k7_subset_1(A_25,B_26,C_27) = k4_xboole_0(B_26,C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [C_27] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_27) = k4_xboole_0('#skF_2',C_27) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_77,plain,(
    ! [A_32,B_33] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_32))),B_33,k1_tarski(k1_xboole_0)) = k2_yellow19(A_32,k3_yellow19(A_32,k2_struct_0(A_32),B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_32)))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_32)))
      | ~ v2_waybel_0(B_33,k3_yellow_1(k2_struct_0(A_32)))
      | v1_xboole_0(B_33)
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_82,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_22,c_66,c_79])).

tff(c_83,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_28,c_82])).

tff(c_18,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_18])).

tff(c_92,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_16,plain,(
    ! [C_17,B_15,A_11] :
      ( ~ v1_xboole_0(C_17)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11))))
      | ~ v13_waybel_0(B_15,k3_yellow_1(A_11))
      | ~ v2_waybel_0(B_15,k3_yellow_1(A_11))
      | ~ v1_subset_1(B_15,u1_struct_0(k3_yellow_1(A_11)))
      | v1_xboole_0(B_15)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_11))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_11))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_11)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_92,c_16])).

tff(c_97,plain,(
    ! [A_11] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_11))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_11))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_11)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_99,plain,(
    ! [A_34] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0(A_34) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_97])).

tff(c_102,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_105,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.19  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.95/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.19  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.95/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.19  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 1.95/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.19  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.95/1.19  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 1.95/1.19  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 1.95/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.95/1.19  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.95/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.19  
% 1.95/1.21  tff(f_105, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 1.95/1.21  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.95/1.21  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.95/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.95/1.21  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.95/1.21  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.95/1.21  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 1.95/1.21  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 1.95/1.21  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_30, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_33, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.21  tff(c_37, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_33])).
% 1.95/1.21  tff(c_42, plain, (![A_20]: (~v1_xboole_0(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.21  tff(c_45, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_42])).
% 1.95/1.21  tff(c_47, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_45])).
% 1.95/1.21  tff(c_48, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_32, c_47])).
% 1.95/1.21  tff(c_26, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_24, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_22, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_28, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.95/1.21  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k1_tarski(B_2))=A_1 | r2_hidden(B_2, A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.21  tff(c_63, plain, (![A_25, B_26, C_27]: (k7_subset_1(A_25, B_26, C_27)=k4_xboole_0(B_26, C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.21  tff(c_66, plain, (![C_27]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_27)=k4_xboole_0('#skF_2', C_27))), inference(resolution, [status(thm)], [c_20, c_63])).
% 1.95/1.21  tff(c_77, plain, (![A_32, B_33]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_32))), B_33, k1_tarski(k1_xboole_0))=k2_yellow19(A_32, k3_yellow19(A_32, k2_struct_0(A_32), B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_32))))) | ~v13_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_32))) | ~v2_waybel_0(B_33, k3_yellow_1(k2_struct_0(A_32))) | v1_xboole_0(B_33) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.21  tff(c_79, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_77])).
% 1.95/1.21  tff(c_82, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_22, c_66, c_79])).
% 1.95/1.21  tff(c_83, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_32, c_28, c_82])).
% 1.95/1.21  tff(c_18, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 1.95/1.21  tff(c_84, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_18])).
% 1.95/1.21  tff(c_92, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 1.95/1.21  tff(c_16, plain, (![C_17, B_15, A_11]: (~v1_xboole_0(C_17) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11)))) | ~v13_waybel_0(B_15, k3_yellow_1(A_11)) | ~v2_waybel_0(B_15, k3_yellow_1(A_11)) | ~v1_subset_1(B_15, u1_struct_0(k3_yellow_1(A_11))) | v1_xboole_0(B_15) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.95/1.21  tff(c_94, plain, (![A_11]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_11)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_11)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_11))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_92, c_16])).
% 1.95/1.21  tff(c_97, plain, (![A_11]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_11)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_11)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_11)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_11))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_94])).
% 1.95/1.21  tff(c_99, plain, (![A_34]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0(A_34))), inference(negUnitSimplification, [status(thm)], [c_28, c_97])).
% 1.95/1.21  tff(c_102, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_99])).
% 1.95/1.21  tff(c_105, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_102])).
% 1.95/1.21  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_105])).
% 1.95/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  Inference rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Ref     : 0
% 1.95/1.21  #Sup     : 16
% 1.95/1.21  #Fact    : 0
% 1.95/1.21  #Define  : 0
% 1.95/1.21  #Split   : 0
% 1.95/1.21  #Chain   : 0
% 1.95/1.21  #Close   : 0
% 1.95/1.21  
% 1.95/1.21  Ordering : KBO
% 1.95/1.21  
% 1.95/1.21  Simplification rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Subsume      : 0
% 1.95/1.21  #Demod        : 10
% 1.95/1.21  #Tautology    : 9
% 1.95/1.21  #SimpNegUnit  : 4
% 1.95/1.21  #BackRed      : 1
% 1.95/1.21  
% 1.95/1.21  #Partial instantiations: 0
% 1.95/1.21  #Strategies tried      : 1
% 1.95/1.21  
% 1.95/1.21  Timing (in seconds)
% 1.95/1.21  ----------------------
% 1.95/1.21  Preprocessing        : 0.31
% 1.95/1.21  Parsing              : 0.16
% 1.95/1.21  CNF conversion       : 0.02
% 1.95/1.21  Main loop            : 0.13
% 1.95/1.21  Inferencing          : 0.05
% 1.95/1.21  Reduction            : 0.04
% 1.95/1.21  Demodulation         : 0.03
% 1.95/1.21  BG Simplification    : 0.01
% 1.95/1.21  Subsumption          : 0.02
% 1.95/1.21  Abstraction          : 0.01
% 1.95/1.21  MUC search           : 0.00
% 1.95/1.21  Cooper               : 0.00
% 1.95/1.21  Total                : 0.46
% 1.95/1.21  Index Insertion      : 0.00
% 1.95/1.21  Index Deletion       : 0.00
% 1.95/1.21  Index Matching       : 0.00
% 1.95/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
