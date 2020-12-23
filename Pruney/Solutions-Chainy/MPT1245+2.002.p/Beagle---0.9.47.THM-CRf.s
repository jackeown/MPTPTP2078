%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 16.37s
% Output     : CNFRefutation 16.37s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 156 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 320 expanded)
%              Number of equality atoms :   21 (  74 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(c_54,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_3'))) != k2_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_594,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(A_108,k3_subset_1(A_108,B_109)) = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_600,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_594])).

tff(c_471,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = k3_subset_1(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_479,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_471])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_688,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_12])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1062,plain,(
    ! [B_133,A_134] :
      ( v4_pre_topc(B_133,A_134)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_134),B_133),A_134)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1065,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_1062])).

tff(c_1067,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1065])).

tff(c_30650,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1067])).

tff(c_30653,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_30650])).

tff(c_30657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_30653])).

tff(c_30658,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1067])).

tff(c_30659,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1067])).

tff(c_44,plain,(
    ! [A_38,B_40] :
      ( k2_pre_topc(A_38,B_40) = B_40
      | ~ v4_pre_topc(B_40,A_38)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30665,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30659,c_44])).

tff(c_30679,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30658,c_30665])).

tff(c_46,plain,(
    ! [A_41,B_43] :
      ( k3_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,k3_subset_1(u1_struct_0(A_41),B_43))) = k1_tops_1(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_61146,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30679,c_46])).

tff(c_61170,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_600,c_61146])).

tff(c_52,plain,(
    ! [A_47,B_49] :
      ( k2_pre_topc(A_47,k1_tops_1(A_47,k2_pre_topc(A_47,k1_tops_1(A_47,B_49)))) = k2_pre_topc(A_47,k1_tops_1(A_47,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_61175,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_3'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_61170,c_52])).

tff(c_61179,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_3'))) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_61170,c_61175])).

tff(c_61181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_61179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 16:25:39 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.37/8.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.37/8.47  
% 16.37/8.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.37/8.47  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 16.37/8.47  
% 16.37/8.47  %Foreground sorts:
% 16.37/8.47  
% 16.37/8.47  
% 16.37/8.47  %Background operators:
% 16.37/8.47  
% 16.37/8.47  
% 16.37/8.47  %Foreground operators:
% 16.37/8.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.37/8.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.37/8.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.37/8.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.37/8.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.37/8.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.37/8.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.37/8.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.37/8.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.37/8.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.37/8.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.37/8.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.37/8.47  tff('#skF_2', type, '#skF_2': $i).
% 16.37/8.47  tff('#skF_3', type, '#skF_3': $i).
% 16.37/8.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.37/8.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 16.37/8.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.37/8.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.37/8.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.37/8.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.37/8.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.37/8.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.37/8.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.37/8.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.37/8.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.37/8.47  
% 16.37/8.48  tff(f_131, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 16.37/8.48  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.37/8.48  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 16.37/8.48  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.37/8.48  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.37/8.48  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 16.37/8.48  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 16.37/8.48  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 16.37/8.48  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 16.37/8.48  tff(c_54, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_3')))!=k2_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.37/8.48  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.37/8.48  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.37/8.48  tff(c_594, plain, (![A_108, B_109]: (k3_subset_1(A_108, k3_subset_1(A_108, B_109))=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.37/8.48  tff(c_600, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_58, c_594])).
% 16.37/8.48  tff(c_471, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=k3_subset_1(A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.37/8.48  tff(c_479, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_58, c_471])).
% 16.37/8.48  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.37/8.48  tff(c_688, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_479, c_12])).
% 16.37/8.48  tff(c_40, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.37/8.48  tff(c_56, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 16.37/8.48  tff(c_1062, plain, (![B_133, A_134]: (v4_pre_topc(B_133, A_134) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_134), B_133), A_134) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.37/8.48  tff(c_1065, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_600, c_1062])).
% 16.37/8.48  tff(c_1067, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1065])).
% 16.37/8.48  tff(c_30650, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1067])).
% 16.37/8.48  tff(c_30653, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_30650])).
% 16.37/8.48  tff(c_30657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_688, c_30653])).
% 16.37/8.48  tff(c_30658, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1067])).
% 16.37/8.48  tff(c_30659, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1067])).
% 16.37/8.48  tff(c_44, plain, (![A_38, B_40]: (k2_pre_topc(A_38, B_40)=B_40 | ~v4_pre_topc(B_40, A_38) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.37/8.48  tff(c_30665, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30659, c_44])).
% 16.37/8.48  tff(c_30679, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30658, c_30665])).
% 16.37/8.48  tff(c_46, plain, (![A_41, B_43]: (k3_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, k3_subset_1(u1_struct_0(A_41), B_43)))=k1_tops_1(A_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.37/8.48  tff(c_61146, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30679, c_46])).
% 16.37/8.48  tff(c_61170, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_600, c_61146])).
% 16.37/8.48  tff(c_52, plain, (![A_47, B_49]: (k2_pre_topc(A_47, k1_tops_1(A_47, k2_pre_topc(A_47, k1_tops_1(A_47, B_49))))=k2_pre_topc(A_47, k1_tops_1(A_47, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_121])).
% 16.37/8.48  tff(c_61175, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_3')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_61170, c_52])).
% 16.37/8.48  tff(c_61179, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_3')))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_61170, c_61175])).
% 16.37/8.48  tff(c_61181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_61179])).
% 16.37/8.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.37/8.48  
% 16.37/8.48  Inference rules
% 16.37/8.48  ----------------------
% 16.37/8.48  #Ref     : 0
% 16.37/8.48  #Sup     : 15283
% 16.37/8.48  #Fact    : 0
% 16.37/8.48  #Define  : 0
% 16.37/8.48  #Split   : 8
% 16.37/8.48  #Chain   : 0
% 16.37/8.48  #Close   : 0
% 16.37/8.48  
% 16.37/8.48  Ordering : KBO
% 16.37/8.48  
% 16.37/8.48  Simplification rules
% 16.37/8.48  ----------------------
% 16.37/8.48  #Subsume      : 1476
% 16.37/8.48  #Demod        : 15980
% 16.37/8.48  #Tautology    : 10473
% 16.37/8.48  #SimpNegUnit  : 166
% 16.37/8.48  #BackRed      : 6
% 16.37/8.48  
% 16.37/8.48  #Partial instantiations: 0
% 16.37/8.48  #Strategies tried      : 1
% 16.37/8.48  
% 16.37/8.48  Timing (in seconds)
% 16.37/8.48  ----------------------
% 16.37/8.48  Preprocessing        : 0.33
% 16.37/8.48  Parsing              : 0.18
% 16.37/8.48  CNF conversion       : 0.02
% 16.37/8.48  Main loop            : 7.38
% 16.37/8.48  Inferencing          : 0.99
% 16.37/8.48  Reduction            : 4.43
% 16.37/8.48  Demodulation         : 3.90
% 16.37/8.48  BG Simplification    : 0.10
% 16.37/8.48  Subsumption          : 1.54
% 16.37/8.48  Abstraction          : 0.17
% 16.37/8.48  MUC search           : 0.00
% 16.37/8.48  Cooper               : 0.00
% 16.37/8.48  Total                : 7.74
% 16.37/8.48  Index Insertion      : 0.00
% 16.37/8.48  Index Deletion       : 0.00
% 16.37/8.48  Index Matching       : 0.00
% 16.37/8.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
