%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 186 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 417 expanded)
%              Number of equality atoms :   28 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_36])).

tff(c_181,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,C_56) = k3_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [B_55] : k9_subset_1(k2_struct_0('#skF_2'),B_55,'#skF_3') = k3_xboole_0(B_55,'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_181])).

tff(c_28,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_200,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_52])).

tff(c_30,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_32])).

tff(c_61,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_61])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_106,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_44] : r1_tarski(A_44,A_44) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,(
    ! [B_61,B_62,A_63] :
      ( k9_subset_1(B_61,B_62,A_63) = k3_xboole_0(B_62,A_63)
      | ~ r1_tarski(A_63,B_61) ) ),
    inference(resolution,[status(thm)],[c_16,c_181])).

tff(c_228,plain,(
    ! [A_44,B_62] : k9_subset_1(A_44,B_62,A_44) = k3_xboole_0(B_62,A_44) ),
    inference(resolution,[status(thm)],[c_111,c_221])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_210,plain,(
    ! [A_59,B_60] :
      ( k2_pre_topc(A_59,B_60) = k2_struct_0(A_59)
      | ~ v1_tops_1(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [B_60] :
      ( k2_pre_topc('#skF_2',B_60) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_60,'#skF_2')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_210])).

tff(c_242,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_2',B_66) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_217])).

tff(c_252,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_242])).

tff(c_257,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_252])).

tff(c_400,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_pre_topc(A_80,k9_subset_1(u1_struct_0(A_80),B_81,k2_pre_topc(A_80,C_82))) = k2_pre_topc(A_80,k9_subset_1(u1_struct_0(A_80),B_81,C_82))
      | ~ v3_pre_topc(B_81,A_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_415,plain,(
    ! [B_81] :
      ( k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_81,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_81,'#skF_3'))
      | ~ v3_pre_topc(B_81,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_400])).

tff(c_2954,plain,(
    ! [B_188] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_188,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_188,'#skF_3'))
      | ~ v3_pre_topc(B_188,'#skF_2')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_51,c_53,c_51,c_228,c_190,c_51,c_51,c_415])).

tff(c_2961,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2954])).

tff(c_2968,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77,c_2961])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_2968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.22  
% 5.77/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.23  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.77/2.23  
% 5.77/2.23  %Foreground sorts:
% 5.77/2.23  
% 5.77/2.23  
% 5.77/2.23  %Background operators:
% 5.77/2.23  
% 5.77/2.23  
% 5.77/2.23  %Foreground operators:
% 5.77/2.23  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.77/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.77/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.77/2.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.77/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.23  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.77/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.77/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.77/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.77/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.77/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.77/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.77/2.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.77/2.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.77/2.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.77/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.23  
% 6.13/2.24  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 6.13/2.24  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.13/2.24  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.13/2.24  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.13/2.24  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.13/2.24  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.13/2.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.13/2.24  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 6.13/2.24  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 6.13/2.24  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.13/2.24  tff(c_42, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.13/2.24  tff(c_47, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_20, c_42])).
% 6.13/2.24  tff(c_51, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_47])).
% 6.13/2.24  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_36])).
% 6.13/2.24  tff(c_181, plain, (![A_54, B_55, C_56]: (k9_subset_1(A_54, B_55, C_56)=k3_xboole_0(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.13/2.24  tff(c_190, plain, (![B_55]: (k9_subset_1(k2_struct_0('#skF_2'), B_55, '#skF_3')=k3_xboole_0(B_55, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_181])).
% 6.13/2.24  tff(c_28, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_52, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 6.13/2.24  tff(c_200, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_52])).
% 6.13/2.24  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_32])).
% 6.13/2.24  tff(c_61, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.13/2.24  tff(c_72, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_61])).
% 6.13/2.24  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.13/2.24  tff(c_77, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_72, c_8])).
% 6.13/2.24  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_106, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.13/2.24  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.13/2.24  tff(c_111, plain, (![A_44]: (r1_tarski(A_44, A_44))), inference(resolution, [status(thm)], [c_106, c_4])).
% 6.13/2.24  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.13/2.24  tff(c_221, plain, (![B_61, B_62, A_63]: (k9_subset_1(B_61, B_62, A_63)=k3_xboole_0(B_62, A_63) | ~r1_tarski(A_63, B_61))), inference(resolution, [status(thm)], [c_16, c_181])).
% 6.13/2.24  tff(c_228, plain, (![A_44, B_62]: (k9_subset_1(A_44, B_62, A_44)=k3_xboole_0(B_62, A_44))), inference(resolution, [status(thm)], [c_111, c_221])).
% 6.13/2.24  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.13/2.24  tff(c_210, plain, (![A_59, B_60]: (k2_pre_topc(A_59, B_60)=k2_struct_0(A_59) | ~v1_tops_1(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.13/2.24  tff(c_217, plain, (![B_60]: (k2_pre_topc('#skF_2', B_60)=k2_struct_0('#skF_2') | ~v1_tops_1(B_60, '#skF_2') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_210])).
% 6.13/2.24  tff(c_242, plain, (![B_66]: (k2_pre_topc('#skF_2', B_66)=k2_struct_0('#skF_2') | ~v1_tops_1(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_217])).
% 6.13/2.24  tff(c_252, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_242])).
% 6.13/2.24  tff(c_257, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_252])).
% 6.13/2.24  tff(c_400, plain, (![A_80, B_81, C_82]: (k2_pre_topc(A_80, k9_subset_1(u1_struct_0(A_80), B_81, k2_pre_topc(A_80, C_82)))=k2_pre_topc(A_80, k9_subset_1(u1_struct_0(A_80), B_81, C_82)) | ~v3_pre_topc(B_81, A_80) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.13/2.24  tff(c_415, plain, (![B_81]: (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_81, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_81, '#skF_3')) | ~v3_pre_topc(B_81, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_400])).
% 6.13/2.24  tff(c_2954, plain, (![B_188]: (k2_pre_topc('#skF_2', k3_xboole_0(B_188, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_188, '#skF_3')) | ~v3_pre_topc(B_188, '#skF_2') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_51, c_53, c_51, c_228, c_190, c_51, c_51, c_415])).
% 6.13/2.24  tff(c_2961, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_2954])).
% 6.13/2.24  tff(c_2968, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77, c_2961])).
% 6.13/2.24  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_2968])).
% 6.13/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.24  
% 6.13/2.24  Inference rules
% 6.13/2.24  ----------------------
% 6.13/2.24  #Ref     : 0
% 6.13/2.24  #Sup     : 699
% 6.13/2.24  #Fact    : 0
% 6.13/2.24  #Define  : 0
% 6.13/2.24  #Split   : 4
% 6.13/2.24  #Chain   : 0
% 6.13/2.24  #Close   : 0
% 6.13/2.24  
% 6.13/2.24  Ordering : KBO
% 6.13/2.24  
% 6.13/2.24  Simplification rules
% 6.13/2.24  ----------------------
% 6.13/2.24  #Subsume      : 110
% 6.13/2.24  #Demod        : 1715
% 6.13/2.24  #Tautology    : 333
% 6.13/2.24  #SimpNegUnit  : 10
% 6.13/2.24  #BackRed      : 4
% 6.13/2.24  
% 6.13/2.24  #Partial instantiations: 0
% 6.13/2.24  #Strategies tried      : 1
% 6.13/2.24  
% 6.13/2.24  Timing (in seconds)
% 6.13/2.24  ----------------------
% 6.13/2.25  Preprocessing        : 0.31
% 6.13/2.25  Parsing              : 0.16
% 6.13/2.25  CNF conversion       : 0.02
% 6.13/2.25  Main loop            : 1.10
% 6.13/2.25  Inferencing          : 0.38
% 6.13/2.25  Reduction            : 0.44
% 6.13/2.25  Demodulation         : 0.35
% 6.13/2.25  BG Simplification    : 0.06
% 6.13/2.25  Subsumption          : 0.16
% 6.13/2.25  Abstraction          : 0.08
% 6.13/2.25  MUC search           : 0.00
% 6.13/2.25  Cooper               : 0.00
% 6.13/2.25  Total                : 1.44
% 6.13/2.25  Index Insertion      : 0.00
% 6.13/2.25  Index Deletion       : 0.00
% 6.13/2.25  Index Matching       : 0.00
% 6.13/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
