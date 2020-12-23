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
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 151 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 394 expanded)
%              Number of equality atoms :   11 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(B_33,k2_pre_topc(A_34,B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_34,B_4,C_5] :
      ( r1_tarski(k9_subset_1(u1_struct_0(A_34),B_4,C_5),k2_pre_topc(A_34,k9_subset_1(u1_struct_0(A_34),B_4,C_5)))
      | ~ l1_pre_topc(A_34)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(u1_struct_0(A_34))) ) ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_51,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_102,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_20,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(k2_pre_topc(A_42,C_43),B_44)
      | ~ r1_tarski(C_43,B_44)
      | ~ v4_pre_topc(B_44,A_42)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    ! [B_44] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_44)
      | ~ r1_tarski('#skF_2',B_44)
      | ~ v4_pre_topc(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_136,plain,(
    ! [B_48] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_48)
      | ~ r1_tarski('#skF_2',B_48)
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_146,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_153,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_146])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_153])).

tff(c_156,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_42,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_48,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_54,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_58,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_18,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(k2_pre_topc(A_35,C_36),B_37)
      | ~ r1_tarski(C_36,B_37)
      | ~ v4_pre_topc(B_37,A_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [B_37] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_37)
      | ~ r1_tarski('#skF_3',B_37)
      | ~ v4_pre_topc(B_37,'#skF_1')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_75,plain,(
    ! [B_38] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),B_38)
      | ~ r1_tarski('#skF_3',B_38)
      | ~ v4_pre_topc(B_38,'#skF_1')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_65])).

tff(c_82,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_89,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_82])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_89])).

tff(c_92,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_16,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_95,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_3') != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_158,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) != k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_95])).

tff(c_185,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(k2_pre_topc(A_55,k9_subset_1(u1_struct_0(A_55),B_56,C_57)),k9_subset_1(u1_struct_0(A_55),k2_pre_topc(A_55,B_56),k2_pre_topc(A_55,C_57)))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_190,plain,(
    ! [C_57] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_57)),k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',C_57)))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_185])).

tff(c_209,plain,(
    ! [C_58] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_58)),k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',C_58)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_190])).

tff(c_217,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_209])).

tff(c_222,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_217])).

tff(c_231,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_234,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_231])).

tff(c_237,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_45,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.24  
% 2.25/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.24  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.25/1.24  
% 2.25/1.24  %Foreground sorts:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Background operators:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Foreground operators:
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.25/1.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.25/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.24  
% 2.25/1.26  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_1)).
% 2.25/1.26  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.25/1.26  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.25/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/1.26  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 2.25/1.26  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 2.25/1.26  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_8, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.26  tff(c_37, plain, (![B_33, A_34]: (r1_tarski(B_33, k2_pre_topc(A_34, B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.26  tff(c_45, plain, (![A_34, B_4, C_5]: (r1_tarski(k9_subset_1(u1_struct_0(A_34), B_4, C_5), k2_pre_topc(A_34, k9_subset_1(u1_struct_0(A_34), B_4, C_5))) | ~l1_pre_topc(A_34) | ~m1_subset_1(C_5, k1_zfmisc_1(u1_struct_0(A_34))))), inference(resolution, [status(thm)], [c_8, c_37])).
% 2.25/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_44, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_37])).
% 2.25/1.26  tff(c_51, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_44])).
% 2.25/1.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.26  tff(c_57, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.25/1.26  tff(c_102, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_57])).
% 2.25/1.26  tff(c_20, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.26  tff(c_107, plain, (![A_42, C_43, B_44]: (r1_tarski(k2_pre_topc(A_42, C_43), B_44) | ~r1_tarski(C_43, B_44) | ~v4_pre_topc(B_44, A_42) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.26  tff(c_114, plain, (![B_44]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_44) | ~r1_tarski('#skF_2', B_44) | ~v4_pre_topc(B_44, '#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_107])).
% 2.25/1.26  tff(c_136, plain, (![B_48]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_48) | ~r1_tarski('#skF_2', B_48) | ~v4_pre_topc(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_114])).
% 2.25/1.26  tff(c_146, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_136])).
% 2.25/1.26  tff(c_153, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_146])).
% 2.25/1.26  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_153])).
% 2.25/1.26  tff(c_156, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_57])).
% 2.25/1.26  tff(c_42, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.25/1.26  tff(c_48, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 2.25/1.26  tff(c_54, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.25/1.26  tff(c_58, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.25/1.26  tff(c_18, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_60, plain, (![A_35, C_36, B_37]: (r1_tarski(k2_pre_topc(A_35, C_36), B_37) | ~r1_tarski(C_36, B_37) | ~v4_pre_topc(B_37, A_35) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.26  tff(c_65, plain, (![B_37]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_37) | ~r1_tarski('#skF_3', B_37) | ~v4_pre_topc(B_37, '#skF_1') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_60])).
% 2.25/1.26  tff(c_75, plain, (![B_38]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), B_38) | ~r1_tarski('#skF_3', B_38) | ~v4_pre_topc(B_38, '#skF_1') | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_65])).
% 2.25/1.26  tff(c_82, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_75])).
% 2.25/1.26  tff(c_89, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_82])).
% 2.25/1.26  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_89])).
% 2.25/1.26  tff(c_92, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 2.25/1.26  tff(c_16, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.26  tff(c_95, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_16])).
% 2.25/1.26  tff(c_158, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))!=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_95])).
% 2.25/1.26  tff(c_185, plain, (![A_55, B_56, C_57]: (r1_tarski(k2_pre_topc(A_55, k9_subset_1(u1_struct_0(A_55), B_56, C_57)), k9_subset_1(u1_struct_0(A_55), k2_pre_topc(A_55, B_56), k2_pre_topc(A_55, C_57))) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.26  tff(c_190, plain, (![C_57]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_57)), k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', C_57))) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_185])).
% 2.25/1.26  tff(c_209, plain, (![C_58]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_58)), k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', C_58))) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_190])).
% 2.25/1.26  tff(c_217, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_209])).
% 2.25/1.26  tff(c_222, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_217])).
% 2.25/1.26  tff(c_231, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_222, c_2])).
% 2.25/1.26  tff(c_234, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_158, c_231])).
% 2.25/1.26  tff(c_237, plain, (~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_45, c_234])).
% 2.25/1.26  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_26, c_237])).
% 2.25/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.26  
% 2.25/1.26  Inference rules
% 2.25/1.26  ----------------------
% 2.25/1.26  #Ref     : 0
% 2.25/1.26  #Sup     : 42
% 2.25/1.26  #Fact    : 0
% 2.25/1.26  #Define  : 0
% 2.25/1.26  #Split   : 3
% 2.25/1.26  #Chain   : 0
% 2.25/1.26  #Close   : 0
% 2.25/1.26  
% 2.25/1.26  Ordering : KBO
% 2.25/1.26  
% 2.25/1.26  Simplification rules
% 2.25/1.26  ----------------------
% 2.25/1.26  #Subsume      : 0
% 2.25/1.26  #Demod        : 44
% 2.25/1.26  #Tautology    : 13
% 2.25/1.26  #SimpNegUnit  : 3
% 2.25/1.26  #BackRed      : 4
% 2.25/1.26  
% 2.25/1.26  #Partial instantiations: 0
% 2.25/1.26  #Strategies tried      : 1
% 2.25/1.26  
% 2.25/1.26  Timing (in seconds)
% 2.25/1.26  ----------------------
% 2.25/1.26  Preprocessing        : 0.29
% 2.25/1.26  Parsing              : 0.16
% 2.25/1.26  CNF conversion       : 0.02
% 2.25/1.26  Main loop            : 0.22
% 2.25/1.26  Inferencing          : 0.07
% 2.25/1.26  Reduction            : 0.08
% 2.25/1.26  Demodulation         : 0.06
% 2.25/1.26  BG Simplification    : 0.01
% 2.25/1.26  Subsumption          : 0.05
% 2.25/1.26  Abstraction          : 0.01
% 2.25/1.26  MUC search           : 0.00
% 2.25/1.26  Cooper               : 0.00
% 2.25/1.26  Total                : 0.54
% 2.25/1.26  Index Insertion      : 0.00
% 2.25/1.26  Index Deletion       : 0.00
% 2.25/1.26  Index Matching       : 0.00
% 2.25/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
