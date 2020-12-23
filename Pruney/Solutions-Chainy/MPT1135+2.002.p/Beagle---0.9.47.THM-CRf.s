%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 168 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 416 expanded)
%              Number of equality atoms :   19 (  86 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
               => ( B = C
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_31,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_85,plain,(
    ! [A_36,B_37] :
      ( m1_pre_topc(k1_pre_topc(A_36,B_37),A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_85])).

tff(c_93,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_89])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_100,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_16])).

tff(c_103,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( v1_pre_topc(k1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_74])).

tff(c_84,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_80])).

tff(c_51,plain,(
    ! [A_33] :
      ( g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)) = A_33
      | ~ v1_pre_topc(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_22])).

tff(c_60,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_32])).

tff(c_132,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_84,c_60])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_45,plain,(
    ! [A_30,B_31] :
      ( l1_pre_topc(g1_pre_topc(A_30,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_16] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_45])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_104,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_104])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_111])).

tff(c_119,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_90,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_170,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_90])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( m1_pre_topc(B_19,A_17)
      | ~ m1_pre_topc(B_19,g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_175,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_190,plain,(
    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_175])).

tff(c_118,plain,(
    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_6,plain,(
    ! [A_2,B_6] :
      ( k2_struct_0(k1_pre_topc(A_2,B_6)) = B_6
      | ~ m1_pre_topc(k1_pre_topc(A_2,B_6),A_2)
      | ~ v1_pre_topc(k1_pre_topc(A_2,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_187,plain,(
    k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_26,c_118,c_172])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_206,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))) = k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_4])).

tff(c_233,plain,(
    ! [A_45] :
      ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc(A_45,'#skF_3')
      | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'),A_45)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_187,c_206])).

tff(c_236,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_233])).

tff(c_245,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31,c_236])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.87/1.22  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.87/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.22  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.87/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.87/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.87/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.22  
% 2.15/1.24  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))) => ((B = C) => (g1_pre_topc(u1_struct_0(k1_pre_topc(A, B)), u1_pre_topc(k1_pre_topc(A, B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_pre_topc)).
% 2.15/1.24  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.15/1.24  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.15/1.24  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.15/1.24  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.15/1.24  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.15/1.24  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.15/1.24  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 2.15/1.24  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.24  tff(c_24, plain, ('#skF_2'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.24  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.24  tff(c_31, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.15/1.24  tff(c_85, plain, (![A_36, B_37]: (m1_pre_topc(k1_pre_topc(A_36, B_37), A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.24  tff(c_89, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31, c_85])).
% 2.15/1.24  tff(c_93, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_89])).
% 2.15/1.24  tff(c_16, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.24  tff(c_100, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_93, c_16])).
% 2.15/1.24  tff(c_103, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_100])).
% 2.15/1.24  tff(c_74, plain, (![A_34, B_35]: (v1_pre_topc(k1_pre_topc(A_34, B_35)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.24  tff(c_80, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31, c_74])).
% 2.15/1.24  tff(c_84, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_80])).
% 2.15/1.24  tff(c_51, plain, (![A_33]: (g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))=A_33 | ~v1_pre_topc(A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.24  tff(c_22, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.24  tff(c_32, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_22])).
% 2.15/1.24  tff(c_60, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_32])).
% 2.15/1.24  tff(c_132, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_84, c_60])).
% 2.15/1.24  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.24  tff(c_45, plain, (![A_30, B_31]: (l1_pre_topc(g1_pre_topc(A_30, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.24  tff(c_49, plain, (![A_16]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_45])).
% 2.15/1.24  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.15/1.24  tff(c_81, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_74])).
% 2.15/1.24  tff(c_104, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_81])).
% 2.15/1.24  tff(c_111, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_49, c_104])).
% 2.15/1.24  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_111])).
% 2.15/1.24  tff(c_119, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_81])).
% 2.15/1.24  tff(c_90, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.15/1.24  tff(c_170, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_90])).
% 2.15/1.24  tff(c_20, plain, (![B_19, A_17]: (m1_pre_topc(B_19, A_17) | ~m1_pre_topc(B_19, g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.15/1.24  tff(c_175, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_170, c_20])).
% 2.15/1.24  tff(c_190, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_175])).
% 2.15/1.24  tff(c_118, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 2.15/1.24  tff(c_6, plain, (![A_2, B_6]: (k2_struct_0(k1_pre_topc(A_2, B_6))=B_6 | ~m1_pre_topc(k1_pre_topc(A_2, B_6), A_2) | ~v1_pre_topc(k1_pre_topc(A_2, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.24  tff(c_172, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_170, c_6])).
% 2.15/1.24  tff(c_187, plain, (k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_26, c_118, c_172])).
% 2.15/1.24  tff(c_4, plain, (![A_2, C_8]: (k1_pre_topc(A_2, k2_struct_0(C_8))=C_8 | ~m1_pre_topc(C_8, A_2) | ~v1_pre_topc(C_8) | ~m1_subset_1(k2_struct_0(C_8), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.24  tff(c_206, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')))=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_187, c_4])).
% 2.15/1.24  tff(c_233, plain, (![A_45]: (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc(A_45, '#skF_3') | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3'), A_45) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_187, c_206])).
% 2.15/1.24  tff(c_236, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_190, c_233])).
% 2.15/1.24  tff(c_245, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_31, c_236])).
% 2.15/1.24  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_245])).
% 2.15/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  Inference rules
% 2.15/1.24  ----------------------
% 2.15/1.24  #Ref     : 0
% 2.15/1.24  #Sup     : 43
% 2.15/1.24  #Fact    : 0
% 2.15/1.24  #Define  : 0
% 2.15/1.24  #Split   : 2
% 2.15/1.24  #Chain   : 0
% 2.15/1.24  #Close   : 0
% 2.15/1.24  
% 2.15/1.24  Ordering : KBO
% 2.15/1.24  
% 2.15/1.24  Simplification rules
% 2.15/1.24  ----------------------
% 2.15/1.24  #Subsume      : 6
% 2.15/1.24  #Demod        : 48
% 2.15/1.24  #Tautology    : 16
% 2.15/1.24  #SimpNegUnit  : 2
% 2.15/1.24  #BackRed      : 0
% 2.15/1.24  
% 2.15/1.24  #Partial instantiations: 0
% 2.15/1.24  #Strategies tried      : 1
% 2.15/1.24  
% 2.15/1.24  Timing (in seconds)
% 2.15/1.24  ----------------------
% 2.15/1.24  Preprocessing        : 0.29
% 2.15/1.24  Parsing              : 0.15
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.19
% 2.15/1.24  Inferencing          : 0.07
% 2.15/1.24  Reduction            : 0.06
% 2.15/1.24  Demodulation         : 0.04
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.24  Subsumption          : 0.03
% 2.15/1.24  Abstraction          : 0.01
% 2.15/1.24  MUC search           : 0.00
% 2.15/1.24  Cooper               : 0.00
% 2.15/1.24  Total                : 0.51
% 2.15/1.24  Index Insertion      : 0.00
% 2.15/1.24  Index Deletion       : 0.00
% 2.15/1.24  Index Matching       : 0.00
% 2.15/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
