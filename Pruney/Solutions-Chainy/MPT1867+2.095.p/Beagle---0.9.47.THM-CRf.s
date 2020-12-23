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
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 186 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v1_pre_topc(B)
          & v2_pre_topc(B)
          & v1_tdlat_3(B)
          & v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_tdlat_3('#skF_1'(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_11] :
      ( m1_pre_topc('#skF_1'(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( m1_subset_1(u1_struct_0(B_10),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [B_62,A_63] :
      ( v2_tex_2(u1_struct_0(B_62),A_63)
      | ~ v1_tdlat_3(B_62)
      | ~ m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc(B_62,A_63)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_116,plain,(
    ! [B_10,A_8] :
      ( v2_tex_2(u1_struct_0(B_10),A_8)
      | ~ v1_tdlat_3(B_10)
      | v2_struct_0(B_10)
      | v2_struct_0(A_8)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_36,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_63,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(resolution,[status(thm)],[c_50,c_63])).

tff(c_123,plain,(
    ! [C_66,A_67,B_68] :
      ( v2_tex_2(C_66,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ r1_tarski(C_66,B_68)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_127,plain,(
    ! [A_67,A_2] :
      ( v2_tex_2('#skF_3',A_67)
      | ~ v2_tex_2(A_2,A_67)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_67,c_123])).

tff(c_132,plain,(
    ! [A_69,A_70] :
      ( v2_tex_2('#skF_3',A_69)
      | ~ v2_tex_2(A_70,A_69)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_127])).

tff(c_147,plain,(
    ! [A_71,B_72] :
      ( v2_tex_2('#skF_3',A_71)
      | ~ v2_tex_2(u1_struct_0(B_72),A_71)
      | ~ m1_pre_topc(B_72,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_170,plain,(
    ! [A_78,B_79] :
      ( v2_tex_2('#skF_3',A_78)
      | ~ v1_tdlat_3(B_79)
      | v2_struct_0(B_79)
      | v2_struct_0(A_78)
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_116,c_147])).

tff(c_174,plain,(
    ! [A_80] :
      ( v2_tex_2('#skF_3',A_80)
      | ~ v1_tdlat_3('#skF_1'(A_80))
      | v2_struct_0('#skF_1'(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_22,plain,(
    ! [A_11] :
      ( ~ v2_struct_0('#skF_1'(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    ! [A_81] :
      ( v2_tex_2('#skF_3',A_81)
      | ~ v1_tdlat_3('#skF_1'(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_174,c_22])).

tff(c_184,plain,(
    ! [A_82] :
      ( v2_tex_2('#skF_3',A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_16,c_179])).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_187,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_32])).

tff(c_190,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.23  
% 2.28/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.23  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.23  
% 2.28/1.23  %Foreground sorts:
% 2.28/1.23  
% 2.28/1.23  
% 2.28/1.23  %Background operators:
% 2.28/1.23  
% 2.28/1.23  
% 2.28/1.23  %Foreground operators:
% 2.28/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.28/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.23  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.28/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.23  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.28/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.23  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.28/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.28/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.28/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.23  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.28/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.23  
% 2.28/1.25  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.28/1.25  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v1_pre_topc(B)) & v2_pre_topc(B)) & v1_tdlat_3(B)) & v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc11_tex_2)).
% 2.28/1.25  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l17_tex_2)).
% 2.28/1.25  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.28/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.28/1.25  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.28/1.25  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.25  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.28/1.25  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.28/1.25  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.28/1.25  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.28/1.25  tff(c_16, plain, (![A_11]: (v1_tdlat_3('#skF_1'(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.25  tff(c_24, plain, (![A_11]: (m1_pre_topc('#skF_1'(A_11), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.25  tff(c_12, plain, (![B_10, A_8]: (m1_subset_1(u1_struct_0(B_10), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.25  tff(c_109, plain, (![B_62, A_63]: (v2_tex_2(u1_struct_0(B_62), A_63) | ~v1_tdlat_3(B_62) | ~m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc(B_62, A_63) | v2_struct_0(B_62) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.25  tff(c_116, plain, (![B_10, A_8]: (v2_tex_2(u1_struct_0(B_10), A_8) | ~v1_tdlat_3(B_10) | v2_struct_0(B_10) | v2_struct_0(A_8) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_12, c_109])).
% 2.28/1.25  tff(c_36, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.28/1.25  tff(c_44, plain, (![A_29]: (k1_xboole_0=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.25  tff(c_48, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.28/1.25  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.25  tff(c_50, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4])).
% 2.28/1.25  tff(c_63, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.25  tff(c_67, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(resolution, [status(thm)], [c_50, c_63])).
% 2.28/1.25  tff(c_123, plain, (![C_66, A_67, B_68]: (v2_tex_2(C_66, A_67) | ~v2_tex_2(B_68, A_67) | ~r1_tarski(C_66, B_68) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.28/1.25  tff(c_127, plain, (![A_67, A_2]: (v2_tex_2('#skF_3', A_67) | ~v2_tex_2(A_2, A_67) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_67, c_123])).
% 2.28/1.25  tff(c_132, plain, (![A_69, A_70]: (v2_tex_2('#skF_3', A_69) | ~v2_tex_2(A_70, A_69) | ~m1_subset_1(A_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_127])).
% 2.28/1.25  tff(c_147, plain, (![A_71, B_72]: (v2_tex_2('#skF_3', A_71) | ~v2_tex_2(u1_struct_0(B_72), A_71) | ~m1_pre_topc(B_72, A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_12, c_132])).
% 2.28/1.25  tff(c_170, plain, (![A_78, B_79]: (v2_tex_2('#skF_3', A_78) | ~v1_tdlat_3(B_79) | v2_struct_0(B_79) | v2_struct_0(A_78) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_116, c_147])).
% 2.28/1.25  tff(c_174, plain, (![A_80]: (v2_tex_2('#skF_3', A_80) | ~v1_tdlat_3('#skF_1'(A_80)) | v2_struct_0('#skF_1'(A_80)) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(resolution, [status(thm)], [c_24, c_170])).
% 2.28/1.25  tff(c_22, plain, (![A_11]: (~v2_struct_0('#skF_1'(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.25  tff(c_179, plain, (![A_81]: (v2_tex_2('#skF_3', A_81) | ~v1_tdlat_3('#skF_1'(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_174, c_22])).
% 2.28/1.25  tff(c_184, plain, (![A_82]: (v2_tex_2('#skF_3', A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_16, c_179])).
% 2.28/1.25  tff(c_32, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.28/1.25  tff(c_187, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_184, c_32])).
% 2.28/1.25  tff(c_190, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_187])).
% 2.28/1.25  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_190])).
% 2.28/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  
% 2.28/1.25  Inference rules
% 2.28/1.25  ----------------------
% 2.28/1.25  #Ref     : 0
% 2.28/1.25  #Sup     : 29
% 2.28/1.25  #Fact    : 0
% 2.28/1.25  #Define  : 0
% 2.28/1.25  #Split   : 0
% 2.28/1.25  #Chain   : 0
% 2.28/1.25  #Close   : 0
% 2.28/1.25  
% 2.28/1.25  Ordering : KBO
% 2.28/1.25  
% 2.28/1.25  Simplification rules
% 2.28/1.25  ----------------------
% 2.28/1.25  #Subsume      : 7
% 2.28/1.25  #Demod        : 6
% 2.28/1.25  #Tautology    : 8
% 2.28/1.25  #SimpNegUnit  : 1
% 2.28/1.25  #BackRed      : 2
% 2.28/1.25  
% 2.28/1.25  #Partial instantiations: 0
% 2.28/1.25  #Strategies tried      : 1
% 2.28/1.25  
% 2.28/1.25  Timing (in seconds)
% 2.28/1.25  ----------------------
% 2.28/1.25  Preprocessing        : 0.29
% 2.28/1.25  Parsing              : 0.16
% 2.28/1.25  CNF conversion       : 0.02
% 2.28/1.25  Main loop            : 0.19
% 2.28/1.25  Inferencing          : 0.08
% 2.28/1.25  Reduction            : 0.05
% 2.28/1.25  Demodulation         : 0.03
% 2.28/1.25  BG Simplification    : 0.01
% 2.28/1.25  Subsumption          : 0.03
% 2.28/1.25  Abstraction          : 0.01
% 2.28/1.25  MUC search           : 0.00
% 2.28/1.25  Cooper               : 0.00
% 2.28/1.25  Total                : 0.51
% 2.28/1.25  Index Insertion      : 0.00
% 2.28/1.25  Index Deletion       : 0.00
% 2.28/1.25  Index Matching       : 0.00
% 2.28/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
