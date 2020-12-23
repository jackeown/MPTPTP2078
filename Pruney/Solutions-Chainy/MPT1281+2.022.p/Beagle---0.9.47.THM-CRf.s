%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:16 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 186 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 407 expanded)
%              Number of equality atoms :   21 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_185,plain,(
    ! [A_91,B_92] :
      ( k2_pre_topc(A_91,k1_tops_1(A_91,B_92)) = B_92
      | ~ v5_tops_1(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_191,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_196,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_191])).

tff(c_34,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_197,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_34])).

tff(c_26,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tops_1(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,(
    ! [A_104,B_105] :
      ( k2_tops_1(A_104,k1_tops_1(A_104,B_105)) = k2_tops_1(A_104,B_105)
      | ~ v5_tops_1(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_293,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_298,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_293])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_302,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_28])).

tff(c_306,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_302])).

tff(c_320,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_323,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_323])).

tff(c_328,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_329,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_20,plain,(
    ! [A_35,B_36,C_37] :
      ( k4_subset_1(A_35,B_36,C_37) = k2_xboole_0(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_518,plain,(
    ! [B_113] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_113,k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_113,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_329,c_20])).

tff(c_537,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_328,c_518])).

tff(c_32,plain,(
    ! [A_48,B_50] :
      ( k4_subset_1(u1_struct_0(A_48),B_50,k2_tops_1(A_48,B_50)) = k2_pre_topc(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_390,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_329,c_32])).

tff(c_417,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_196,c_298,c_390])).

tff(c_18,plain,(
    ! [A_32,C_34,B_33] :
      ( k4_subset_1(A_32,C_34,B_33) = k4_subset_1(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_663,plain,(
    ! [B_117] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),B_117) = k4_subset_1(u1_struct_0('#skF_1'),B_117,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_328,c_18])).

tff(c_666,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_329,c_663])).

tff(c_682,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_417,c_666])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_719,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_2])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.15/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.15/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.15/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.15/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.47  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.15/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.47  
% 3.15/1.48  tff(f_100, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 3.15/1.48  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 3.15/1.48  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.15/1.48  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 3.15/1.48  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.15/1.48  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.15/1.48  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.15/1.48  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 3.15/1.48  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.15/1.48  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.48  tff(c_36, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.48  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.48  tff(c_185, plain, (![A_91, B_92]: (k2_pre_topc(A_91, k1_tops_1(A_91, B_92))=B_92 | ~v5_tops_1(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.48  tff(c_191, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_185])).
% 3.15/1.48  tff(c_196, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_191])).
% 3.15/1.48  tff(c_34, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.48  tff(c_197, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_34])).
% 3.15/1.48  tff(c_26, plain, (![A_41, B_42]: (m1_subset_1(k1_tops_1(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.48  tff(c_287, plain, (![A_104, B_105]: (k2_tops_1(A_104, k1_tops_1(A_104, B_105))=k2_tops_1(A_104, B_105) | ~v5_tops_1(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.48  tff(c_293, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_287])).
% 3.15/1.48  tff(c_298, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_293])).
% 3.15/1.48  tff(c_28, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.48  tff(c_302, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_298, c_28])).
% 3.15/1.48  tff(c_306, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_302])).
% 3.15/1.48  tff(c_320, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_306])).
% 3.15/1.48  tff(c_323, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_320])).
% 3.15/1.48  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_323])).
% 3.15/1.48  tff(c_328, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_306])).
% 3.15/1.48  tff(c_329, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_306])).
% 3.15/1.48  tff(c_20, plain, (![A_35, B_36, C_37]: (k4_subset_1(A_35, B_36, C_37)=k2_xboole_0(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.48  tff(c_518, plain, (![B_113]: (k4_subset_1(u1_struct_0('#skF_1'), B_113, k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_113, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_329, c_20])).
% 3.15/1.48  tff(c_537, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_328, c_518])).
% 3.15/1.48  tff(c_32, plain, (![A_48, B_50]: (k4_subset_1(u1_struct_0(A_48), B_50, k2_tops_1(A_48, B_50))=k2_pre_topc(A_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.48  tff(c_390, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_329, c_32])).
% 3.15/1.48  tff(c_417, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_196, c_298, c_390])).
% 3.15/1.48  tff(c_18, plain, (![A_32, C_34, B_33]: (k4_subset_1(A_32, C_34, B_33)=k4_subset_1(A_32, B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.48  tff(c_663, plain, (![B_117]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), B_117)=k4_subset_1(u1_struct_0('#skF_1'), B_117, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_328, c_18])).
% 3.15/1.48  tff(c_666, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_329, c_663])).
% 3.15/1.48  tff(c_682, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_537, c_417, c_666])).
% 3.15/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.48  tff(c_719, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_682, c_2])).
% 3.15/1.48  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_719])).
% 3.15/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  Inference rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Ref     : 0
% 3.15/1.48  #Sup     : 168
% 3.15/1.48  #Fact    : 0
% 3.15/1.48  #Define  : 0
% 3.15/1.48  #Split   : 3
% 3.15/1.48  #Chain   : 0
% 3.15/1.48  #Close   : 0
% 3.15/1.48  
% 3.15/1.48  Ordering : KBO
% 3.15/1.48  
% 3.15/1.48  Simplification rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Subsume      : 6
% 3.15/1.48  #Demod        : 105
% 3.15/1.48  #Tautology    : 84
% 3.15/1.48  #SimpNegUnit  : 1
% 3.15/1.48  #BackRed      : 5
% 3.15/1.48  
% 3.15/1.48  #Partial instantiations: 0
% 3.15/1.49  #Strategies tried      : 1
% 3.15/1.49  
% 3.15/1.49  Timing (in seconds)
% 3.15/1.49  ----------------------
% 3.15/1.49  Preprocessing        : 0.35
% 3.15/1.49  Parsing              : 0.19
% 3.15/1.49  CNF conversion       : 0.02
% 3.15/1.49  Main loop            : 0.37
% 3.15/1.49  Inferencing          : 0.14
% 3.15/1.49  Reduction            : 0.12
% 3.15/1.49  Demodulation         : 0.08
% 3.15/1.49  BG Simplification    : 0.02
% 3.15/1.49  Subsumption          : 0.07
% 3.15/1.49  Abstraction          : 0.03
% 3.15/1.49  MUC search           : 0.00
% 3.15/1.49  Cooper               : 0.00
% 3.15/1.49  Total                : 0.75
% 3.15/1.49  Index Insertion      : 0.00
% 3.15/1.49  Index Deletion       : 0.00
% 3.15/1.49  Index Matching       : 0.00
% 3.15/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
