%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 138 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 558 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k1_pre_topc(A,B))
        & v1_pre_topc(k1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_67,plain,(
    ! [A_30,B_31] :
      ( ~ v2_struct_0(k1_pre_topc(A_30,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,
    ( ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_76,plain,
    ( ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_73])).

tff(c_77,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_26,c_76])).

tff(c_33,plain,(
    ! [A_23,B_24] :
      ( v1_pre_topc(k1_pre_topc(A_23,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_39,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( m1_pre_topc(k1_pre_topc(A_28,B_29),A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_65,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_40,plain,(
    ! [A_25,B_26] :
      ( u1_struct_0(k1_pre_topc(A_25,B_26)) = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_46,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_22,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_78,plain,(
    ! [B_32,A_33] :
      ( u1_struct_0(B_32) = '#skF_1'(A_33,B_32)
      | v4_tex_2(B_32,A_33)
      | ~ m1_pre_topc(B_32,A_33)
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [C_22] :
      ( u1_struct_0(C_22) != '#skF_3'
      | ~ v4_tex_2(C_22,'#skF_2')
      | ~ m1_pre_topc(C_22,'#skF_2')
      | ~ v1_pre_topc(C_22)
      | v2_struct_0(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,(
    ! [B_32] :
      ( u1_struct_0(B_32) != '#skF_3'
      | ~ v1_pre_topc(B_32)
      | v2_struct_0(B_32)
      | u1_struct_0(B_32) = '#skF_1'('#skF_2',B_32)
      | ~ m1_pre_topc(B_32,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_20])).

tff(c_85,plain,(
    ! [B_32] :
      ( u1_struct_0(B_32) != '#skF_3'
      | ~ v1_pre_topc(B_32)
      | v2_struct_0(B_32)
      | u1_struct_0(B_32) = '#skF_1'('#skF_2',B_32)
      | ~ m1_pre_topc(B_32,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_82])).

tff(c_88,plain,(
    ! [B_36] :
      ( u1_struct_0(B_36) != '#skF_3'
      | ~ v1_pre_topc(B_36)
      | v2_struct_0(B_36)
      | u1_struct_0(B_36) = '#skF_1'('#skF_2',B_36)
      | ~ m1_pre_topc(B_36,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_85])).

tff(c_91,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_65,c_88])).

tff(c_94,plain,
    ( v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_39,c_46,c_91])).

tff(c_95,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_94])).

tff(c_14,plain,(
    ! [A_8,B_14] :
      ( ~ v3_tex_2('#skF_1'(A_8,B_14),A_8)
      | v4_tex_2(B_14,A_8)
      | ~ m1_pre_topc(B_14,A_8)
      | ~ l1_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,
    ( ~ v3_tex_2('#skF_3','#skF_2')
    | v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_14])).

tff(c_103,plain,
    ( v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_65,c_22,c_99])).

tff(c_104,plain,(
    v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_103])).

tff(c_108,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_104,c_20])).

tff(c_111,plain,(
    v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_65,c_46,c_108])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.17  
% 2.05/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.17  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.17  
% 2.05/1.17  %Foreground sorts:
% 2.05/1.17  
% 2.05/1.17  
% 2.05/1.17  %Background operators:
% 2.05/1.17  
% 2.05/1.17  
% 2.05/1.17  %Foreground operators:
% 2.05/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.05/1.17  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.05/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.17  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.05/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.05/1.17  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.05/1.17  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.17  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.17  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.05/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.05/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.05/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.05/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.17  
% 2.16/1.19  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 2.16/1.19  tff(f_48, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (~v2_struct_0(k1_pre_topc(A, B)) & v1_pre_topc(k1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_pre_topc)).
% 2.16/1.19  tff(f_33, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.16/1.19  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.16/1.19  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 2.16/1.19  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_26, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_67, plain, (![A_30, B_31]: (~v2_struct_0(k1_pre_topc(A_30, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.19  tff(c_73, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.16/1.19  tff(c_76, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_73])).
% 2.16/1.19  tff(c_77, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_26, c_76])).
% 2.16/1.19  tff(c_33, plain, (![A_23, B_24]: (v1_pre_topc(k1_pre_topc(A_23, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.19  tff(c_36, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.16/1.19  tff(c_39, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 2.16/1.19  tff(c_58, plain, (![A_28, B_29]: (m1_pre_topc(k1_pre_topc(A_28, B_29), A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.19  tff(c_62, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_58])).
% 2.16/1.19  tff(c_65, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_62])).
% 2.16/1.19  tff(c_40, plain, (![A_25, B_26]: (u1_struct_0(k1_pre_topc(A_25, B_26))=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.19  tff(c_43, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.16/1.19  tff(c_46, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_43])).
% 2.16/1.19  tff(c_22, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_78, plain, (![B_32, A_33]: (u1_struct_0(B_32)='#skF_1'(A_33, B_32) | v4_tex_2(B_32, A_33) | ~m1_pre_topc(B_32, A_33) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.19  tff(c_20, plain, (![C_22]: (u1_struct_0(C_22)!='#skF_3' | ~v4_tex_2(C_22, '#skF_2') | ~m1_pre_topc(C_22, '#skF_2') | ~v1_pre_topc(C_22) | v2_struct_0(C_22))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.16/1.19  tff(c_82, plain, (![B_32]: (u1_struct_0(B_32)!='#skF_3' | ~v1_pre_topc(B_32) | v2_struct_0(B_32) | u1_struct_0(B_32)='#skF_1'('#skF_2', B_32) | ~m1_pre_topc(B_32, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_20])).
% 2.16/1.19  tff(c_85, plain, (![B_32]: (u1_struct_0(B_32)!='#skF_3' | ~v1_pre_topc(B_32) | v2_struct_0(B_32) | u1_struct_0(B_32)='#skF_1'('#skF_2', B_32) | ~m1_pre_topc(B_32, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_82])).
% 2.16/1.19  tff(c_88, plain, (![B_36]: (u1_struct_0(B_36)!='#skF_3' | ~v1_pre_topc(B_36) | v2_struct_0(B_36) | u1_struct_0(B_36)='#skF_1'('#skF_2', B_36) | ~m1_pre_topc(B_36, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_85])).
% 2.16/1.19  tff(c_91, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_65, c_88])).
% 2.16/1.19  tff(c_94, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | '#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_39, c_46, c_91])).
% 2.16/1.19  tff(c_95, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_77, c_94])).
% 2.16/1.19  tff(c_14, plain, (![A_8, B_14]: (~v3_tex_2('#skF_1'(A_8, B_14), A_8) | v4_tex_2(B_14, A_8) | ~m1_pre_topc(B_14, A_8) | ~l1_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.19  tff(c_99, plain, (~v3_tex_2('#skF_3', '#skF_2') | v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_95, c_14])).
% 2.16/1.19  tff(c_103, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_65, c_22, c_99])).
% 2.16/1.19  tff(c_104, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_103])).
% 2.16/1.19  tff(c_108, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_104, c_20])).
% 2.16/1.19  tff(c_111, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_65, c_46, c_108])).
% 2.16/1.19  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_111])).
% 2.16/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.19  
% 2.16/1.19  Inference rules
% 2.16/1.19  ----------------------
% 2.16/1.19  #Ref     : 0
% 2.16/1.19  #Sup     : 16
% 2.16/1.19  #Fact    : 0
% 2.16/1.19  #Define  : 0
% 2.16/1.19  #Split   : 1
% 2.16/1.19  #Chain   : 0
% 2.16/1.19  #Close   : 0
% 2.16/1.19  
% 2.16/1.19  Ordering : KBO
% 2.16/1.19  
% 2.16/1.19  Simplification rules
% 2.16/1.19  ----------------------
% 2.16/1.19  #Subsume      : 2
% 2.16/1.19  #Demod        : 14
% 2.16/1.19  #Tautology    : 4
% 2.16/1.19  #SimpNegUnit  : 5
% 2.16/1.19  #BackRed      : 0
% 2.16/1.19  
% 2.16/1.19  #Partial instantiations: 0
% 2.16/1.19  #Strategies tried      : 1
% 2.16/1.19  
% 2.16/1.19  Timing (in seconds)
% 2.16/1.19  ----------------------
% 2.16/1.19  Preprocessing        : 0.30
% 2.16/1.19  Parsing              : 0.15
% 2.16/1.19  CNF conversion       : 0.02
% 2.16/1.19  Main loop            : 0.13
% 2.16/1.19  Inferencing          : 0.05
% 2.16/1.19  Reduction            : 0.04
% 2.16/1.19  Demodulation         : 0.03
% 2.16/1.19  BG Simplification    : 0.01
% 2.16/1.19  Subsumption          : 0.02
% 2.16/1.19  Abstraction          : 0.01
% 2.16/1.19  MUC search           : 0.00
% 2.16/1.19  Cooper               : 0.00
% 2.16/1.19  Total                : 0.45
% 2.16/1.19  Index Insertion      : 0.00
% 2.16/1.19  Index Deletion       : 0.00
% 2.16/1.19  Index Matching       : 0.00
% 2.16/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
