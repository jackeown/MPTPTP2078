%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 196 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 491 expanded)
%              Number of equality atoms :   19 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
               => ( B = C
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_33,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_87,plain,(
    ! [A_36,B_37] :
      ( m1_pre_topc(k1_pre_topc(A_36,B_37),A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_87])).

tff(c_95,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_102,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_105,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0(B_19),u1_pre_topc(B_19)))
      | ~ m1_pre_topc(A_17,B_19)
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( v1_pre_topc(k1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_76])).

tff(c_86,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_53,plain,(
    ! [A_33] :
      ( g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)) = A_33
      | ~ v1_pre_topc(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_24])).

tff(c_62,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_34])).

tff(c_145,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_86,c_62])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    ! [A_27,B_28] :
      ( l1_pre_topc(g1_pre_topc(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    ! [A_16] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_83,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_118,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_124,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_118])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124])).

tff(c_132,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_152,plain,(
    ! [A_44,B_45] :
      ( k2_struct_0(k1_pre_topc(A_44,B_45)) = B_45
      | ~ m1_pre_topc(k1_pre_topc(A_44,B_45),A_44)
      | ~ v1_pre_topc(k1_pre_topc(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_152])).

tff(c_161,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_33,c_86,c_157])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_165,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_4])).

tff(c_171,plain,(
    ! [A_46] :
      ( k1_pre_topc(A_46,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_46)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_161,c_165])).

tff(c_174,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_180,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_174])).

tff(c_181,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_180])).

tff(c_236,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_181])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_32,c_95,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.28  
% 2.13/1.28  %Foreground sorts:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Background operators:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Foreground operators:
% 2.13/1.28  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.13/1.28  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.28  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.13/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.28  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.13/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.13/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.13/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.28  
% 2.13/1.30  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))) => ((B = C) => (g1_pre_topc(u1_struct_0(k1_pre_topc(A, B)), u1_pre_topc(k1_pre_topc(A, B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_pre_topc)).
% 2.13/1.30  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.13/1.30  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.13/1.30  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.13/1.30  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.13/1.30  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.13/1.30  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.13/1.30  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 2.13/1.30  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.13/1.30  tff(c_26, plain, ('#skF_2'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.13/1.30  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.13/1.30  tff(c_33, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.13/1.30  tff(c_87, plain, (![A_36, B_37]: (m1_pre_topc(k1_pre_topc(A_36, B_37), A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.30  tff(c_91, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_87])).
% 2.13/1.30  tff(c_95, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 2.13/1.30  tff(c_16, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.30  tff(c_102, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_16])).
% 2.13/1.30  tff(c_105, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_102])).
% 2.13/1.30  tff(c_22, plain, (![A_17, B_19]: (m1_pre_topc(A_17, g1_pre_topc(u1_struct_0(B_19), u1_pre_topc(B_19))) | ~m1_pre_topc(A_17, B_19) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.13/1.30  tff(c_76, plain, (![A_34, B_35]: (v1_pre_topc(k1_pre_topc(A_34, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.30  tff(c_82, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_76])).
% 2.13/1.30  tff(c_86, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_82])).
% 2.13/1.30  tff(c_53, plain, (![A_33]: (g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))=A_33 | ~v1_pre_topc(A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.30  tff(c_24, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.13/1.30  tff(c_34, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_24])).
% 2.13/1.30  tff(c_62, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_34])).
% 2.13/1.30  tff(c_145, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_86, c_62])).
% 2.13/1.30  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.30  tff(c_41, plain, (![A_27, B_28]: (l1_pre_topc(g1_pre_topc(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.30  tff(c_45, plain, (![A_16]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.13/1.30  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.13/1.30  tff(c_83, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.13/1.30  tff(c_118, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_83])).
% 2.13/1.30  tff(c_124, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_45, c_118])).
% 2.13/1.30  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_124])).
% 2.13/1.30  tff(c_132, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_83])).
% 2.13/1.30  tff(c_152, plain, (![A_44, B_45]: (k2_struct_0(k1_pre_topc(A_44, B_45))=B_45 | ~m1_pre_topc(k1_pre_topc(A_44, B_45), A_44) | ~v1_pre_topc(k1_pre_topc(A_44, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.30  tff(c_157, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_152])).
% 2.13/1.30  tff(c_161, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_33, c_86, c_157])).
% 2.13/1.30  tff(c_4, plain, (![A_2, C_8]: (k1_pre_topc(A_2, k2_struct_0(C_8))=C_8 | ~m1_pre_topc(C_8, A_2) | ~v1_pre_topc(C_8) | ~m1_subset_1(k2_struct_0(C_8), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.30  tff(c_165, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_161, c_4])).
% 2.13/1.30  tff(c_171, plain, (![A_46]: (k1_pre_topc(A_46, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_46) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_161, c_165])).
% 2.13/1.30  tff(c_174, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_171])).
% 2.13/1.30  tff(c_180, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_174])).
% 2.13/1.30  tff(c_181, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_145, c_180])).
% 2.13/1.30  tff(c_236, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_181])).
% 2.13/1.30  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_32, c_95, c_236])).
% 2.13/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  Inference rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Ref     : 0
% 2.13/1.30  #Sup     : 43
% 2.13/1.30  #Fact    : 0
% 2.13/1.30  #Define  : 0
% 2.13/1.30  #Split   : 1
% 2.13/1.30  #Chain   : 0
% 2.13/1.30  #Close   : 0
% 2.13/1.30  
% 2.13/1.30  Ordering : KBO
% 2.13/1.30  
% 2.13/1.30  Simplification rules
% 2.13/1.30  ----------------------
% 2.13/1.30  #Subsume      : 5
% 2.13/1.30  #Demod        : 43
% 2.13/1.30  #Tautology    : 17
% 2.13/1.30  #SimpNegUnit  : 1
% 2.13/1.30  #BackRed      : 0
% 2.13/1.30  
% 2.13/1.30  #Partial instantiations: 0
% 2.13/1.30  #Strategies tried      : 1
% 2.13/1.30  
% 2.13/1.30  Timing (in seconds)
% 2.13/1.30  ----------------------
% 2.13/1.30  Preprocessing        : 0.32
% 2.13/1.30  Parsing              : 0.17
% 2.13/1.30  CNF conversion       : 0.02
% 2.13/1.30  Main loop            : 0.20
% 2.13/1.30  Inferencing          : 0.07
% 2.13/1.30  Reduction            : 0.07
% 2.13/1.30  Demodulation         : 0.05
% 2.13/1.30  BG Simplification    : 0.01
% 2.13/1.30  Subsumption          : 0.04
% 2.13/1.30  Abstraction          : 0.01
% 2.13/1.30  MUC search           : 0.00
% 2.13/1.30  Cooper               : 0.00
% 2.13/1.30  Total                : 0.56
% 2.13/1.30  Index Insertion      : 0.00
% 2.13/1.30  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
