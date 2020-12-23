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
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 348 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [B_42,A_43] :
      ( v2_tops_1(B_42,A_43)
      | k1_tops_1(A_43,B_42) != k1_xboole_0
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_119,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_120,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_119])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tops_1(A_34,B_35),B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_79,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_76])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_99,plain,(
    ! [A_40,B_41] :
      ( v3_pre_topc(k1_tops_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_99])).

tff(c_107,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_103])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tops_1(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [C_28] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_28
      | ~ v3_pre_topc(C_28,'#skF_1')
      | ~ r1_tarski(C_28,'#skF_2')
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    ! [C_44] :
      ( k1_xboole_0 = C_44
      | ~ v3_pre_topc(C_44,'#skF_1')
      | ~ r1_tarski(C_44,'#skF_2')
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46])).

tff(c_126,plain,(
    ! [B_5] :
      ( k1_tops_1('#skF_1',B_5) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_5),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_5),'#skF_2')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_122])).

tff(c_177,plain,(
    ! [B_57] :
      ( k1_tops_1('#skF_1',B_57) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_57),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_57),'#skF_2')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126])).

tff(c_184,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_190,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_107,c_184])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_190])).

tff(c_193,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_194,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_198,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_30])).

tff(c_32,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_34,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_213,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_34])).

tff(c_284,plain,(
    ! [A_69,B_70] :
      ( k1_tops_1(A_69,B_70) = k1_xboole_0
      | ~ v2_tops_1(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_293,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_284])).

tff(c_301,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194,c_293])).

tff(c_421,plain,(
    ! [B_77,A_78,C_79] :
      ( r1_tarski(B_77,k1_tops_1(A_78,C_79))
      | ~ r1_tarski(B_77,C_79)
      | ~ v3_pre_topc(B_77,A_78)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_429,plain,(
    ! [B_77] :
      ( r1_tarski(B_77,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_77,'#skF_2')
      | ~ v3_pre_topc(B_77,'#skF_1')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_421])).

tff(c_440,plain,(
    ! [B_80] :
      ( r1_tarski(B_80,k1_xboole_0)
      | ~ r1_tarski(B_80,'#skF_2')
      | ~ v3_pre_topc(B_80,'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_301,c_429])).

tff(c_450,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_213,c_440])).

tff(c_462,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_196,c_450])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_469,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_462,c_211])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.39  
% 2.49/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.39  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.39  
% 2.49/1.39  %Foreground sorts:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Background operators:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Foreground operators:
% 2.49/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.39  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.49/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.49/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.39  
% 2.81/1.41  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 2.81/1.41  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.81/1.41  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.81/1.41  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.81/1.41  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.81/1.41  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.81/1.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.81/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.41  tff(c_28, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_50, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_109, plain, (![B_42, A_43]: (v2_tops_1(B_42, A_43) | k1_tops_1(A_43, B_42)!=k1_xboole_0 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.41  tff(c_115, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_109])).
% 2.81/1.41  tff(c_119, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_115])).
% 2.81/1.41  tff(c_120, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_119])).
% 2.81/1.41  tff(c_74, plain, (![A_34, B_35]: (r1_tarski(k1_tops_1(A_34, B_35), B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.41  tff(c_76, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.81/1.41  tff(c_79, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_76])).
% 2.81/1.41  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_99, plain, (![A_40, B_41]: (v3_pre_topc(k1_tops_1(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.41  tff(c_103, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_99])).
% 2.81/1.41  tff(c_107, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_103])).
% 2.81/1.41  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(k1_tops_1(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.41  tff(c_46, plain, (![C_28]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_28 | ~v3_pre_topc(C_28, '#skF_1') | ~r1_tarski(C_28, '#skF_2') | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_122, plain, (![C_44]: (k1_xboole_0=C_44 | ~v3_pre_topc(C_44, '#skF_1') | ~r1_tarski(C_44, '#skF_2') | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_46])).
% 2.81/1.41  tff(c_126, plain, (![B_5]: (k1_tops_1('#skF_1', B_5)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_5), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_5), '#skF_2') | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_122])).
% 2.81/1.41  tff(c_177, plain, (![B_57]: (k1_tops_1('#skF_1', B_57)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_57), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_57), '#skF_2') | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126])).
% 2.81/1.41  tff(c_184, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_177])).
% 2.81/1.41  tff(c_190, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79, c_107, c_184])).
% 2.81/1.41  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_190])).
% 2.81/1.41  tff(c_193, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_194, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_30, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_198, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_30])).
% 2.81/1.41  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_196, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_32])).
% 2.81/1.41  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.81/1.41  tff(c_213, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_34])).
% 2.81/1.41  tff(c_284, plain, (![A_69, B_70]: (k1_tops_1(A_69, B_70)=k1_xboole_0 | ~v2_tops_1(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.41  tff(c_293, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_284])).
% 2.81/1.41  tff(c_301, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194, c_293])).
% 2.81/1.41  tff(c_421, plain, (![B_77, A_78, C_79]: (r1_tarski(B_77, k1_tops_1(A_78, C_79)) | ~r1_tarski(B_77, C_79) | ~v3_pre_topc(B_77, A_78) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.41  tff(c_429, plain, (![B_77]: (r1_tarski(B_77, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_77, '#skF_2') | ~v3_pre_topc(B_77, '#skF_1') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_421])).
% 2.81/1.41  tff(c_440, plain, (![B_80]: (r1_tarski(B_80, k1_xboole_0) | ~r1_tarski(B_80, '#skF_2') | ~v3_pre_topc(B_80, '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_301, c_429])).
% 2.81/1.41  tff(c_450, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_213, c_440])).
% 2.81/1.41  tff(c_462, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_196, c_450])).
% 2.81/1.41  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.41  tff(c_199, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.41  tff(c_211, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_199])).
% 2.81/1.41  tff(c_469, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_462, c_211])).
% 2.81/1.41  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_469])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 0
% 2.81/1.41  #Sup     : 76
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 10
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 9
% 2.81/1.41  #Demod        : 109
% 2.81/1.41  #Tautology    : 33
% 2.81/1.41  #SimpNegUnit  : 7
% 2.81/1.41  #BackRed      : 5
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.41  Preprocessing        : 0.31
% 2.81/1.41  Parsing              : 0.16
% 2.81/1.41  CNF conversion       : 0.02
% 2.81/1.41  Main loop            : 0.29
% 2.81/1.41  Inferencing          : 0.10
% 2.81/1.41  Reduction            : 0.09
% 2.81/1.41  Demodulation         : 0.06
% 2.81/1.41  BG Simplification    : 0.02
% 2.81/1.41  Subsumption          : 0.06
% 2.81/1.41  Abstraction          : 0.01
% 2.81/1.41  MUC search           : 0.00
% 2.81/1.41  Cooper               : 0.00
% 2.81/1.41  Total                : 0.63
% 2.81/1.41  Index Insertion      : 0.00
% 2.81/1.41  Index Deletion       : 0.00
% 2.81/1.41  Index Matching       : 0.00
% 2.81/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
