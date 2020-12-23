%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:22 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 200 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  121 ( 404 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_10,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_73,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(A_59,B_60,C_61) = k3_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_10,B_60] : k9_subset_1(A_10,B_60,'#skF_4') = k3_xboole_0(B_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_86,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k9_subset_1(A_64,B_65,C_66),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [B_60,A_10] :
      ( m1_subset_1(k3_xboole_0(B_60,'#skF_4'),k1_zfmisc_1(A_10))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_86])).

tff(c_102,plain,(
    ! [B_67,A_68] : m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    ! [B_67,A_68] :
      ( v1_xboole_0(k3_xboole_0(B_67,'#skF_4'))
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_102,c_12])).

tff(c_131,plain,(
    ! [A_68] : ~ v1_xboole_0(A_68) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_34])).

tff(c_136,plain,(
    ! [B_71] : v1_xboole_0(k3_xboole_0(B_71,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_140,plain,(
    ! [B_71] : k3_xboole_0(B_71,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_47])).

tff(c_165,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2'(A_75,B_76),B_76)
      | v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_176,plain,(
    ! [A_78] :
      ( r1_tarski('#skF_2'(A_78,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_48,c_165])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_xboole_0(A_2,B_3) = A_2
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_78] :
      ( k3_xboole_0('#skF_2'(A_78,'#skF_4'),'#skF_4') = '#skF_2'(A_78,'#skF_4')
      | v2_tex_2('#skF_4',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_200,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_179])).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_203,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_30])).

tff(c_206,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203])).

tff(c_113,plain,(
    ! [B_69,A_70] :
      ( v4_pre_topc(B_69,A_70)
      | ~ v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_125,plain,(
    ! [A_70] :
      ( v4_pre_topc('#skF_4',A_70)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_130,plain,(
    ! [A_70] :
      ( v4_pre_topc('#skF_4',A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_143,plain,(
    ! [A_10,B_60] : k9_subset_1(A_10,B_60,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_76])).

tff(c_387,plain,(
    ! [A_115,B_116,D_117] :
      ( k9_subset_1(u1_struct_0(A_115),B_116,D_117) != '#skF_2'(A_115,B_116)
      | ~ v4_pre_topc(D_117,A_115)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_393,plain,(
    ! [A_115,B_60] :
      ( '#skF_2'(A_115,B_60) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_115)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_115)))
      | v2_tex_2(B_60,A_115)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_387])).

tff(c_396,plain,(
    ! [A_118,B_119] :
      ( '#skF_2'(A_118,B_119) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_118)
      | v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_393])).

tff(c_415,plain,(
    ! [A_120] :
      ( '#skF_2'(A_120,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_120)
      | v2_tex_2('#skF_4',A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_48,c_396])).

tff(c_420,plain,(
    ! [A_121] :
      ( '#skF_2'(A_121,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_130,c_415])).

tff(c_423,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_420,c_30])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_206,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.39  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.53/1.39  
% 2.53/1.39  %Foreground sorts:
% 2.53/1.39  
% 2.53/1.39  
% 2.53/1.39  %Background operators:
% 2.53/1.39  
% 2.53/1.39  
% 2.53/1.39  %Foreground operators:
% 2.53/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.53/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.53/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.39  
% 2.53/1.41  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.53/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.41  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.41  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.53/1.41  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.53/1.41  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.53/1.41  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.53/1.41  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.53/1.41  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.53/1.41  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.53/1.41  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.53/1.41  tff(c_34, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.53/1.41  tff(c_42, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.41  tff(c_46, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.53/1.41  tff(c_10, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.41  tff(c_48, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 2.53/1.41  tff(c_73, plain, (![A_59, B_60, C_61]: (k9_subset_1(A_59, B_60, C_61)=k3_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.41  tff(c_76, plain, (![A_10, B_60]: (k9_subset_1(A_10, B_60, '#skF_4')=k3_xboole_0(B_60, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 2.53/1.41  tff(c_86, plain, (![A_64, B_65, C_66]: (m1_subset_1(k9_subset_1(A_64, B_65, C_66), k1_zfmisc_1(A_64)) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.41  tff(c_96, plain, (![B_60, A_10]: (m1_subset_1(k3_xboole_0(B_60, '#skF_4'), k1_zfmisc_1(A_10)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_86])).
% 2.53/1.41  tff(c_102, plain, (![B_67, A_68]: (m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_96])).
% 2.53/1.41  tff(c_12, plain, (![B_13, A_11]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.41  tff(c_112, plain, (![B_67, A_68]: (v1_xboole_0(k3_xboole_0(B_67, '#skF_4')) | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_102, c_12])).
% 2.53/1.41  tff(c_131, plain, (![A_68]: (~v1_xboole_0(A_68))), inference(splitLeft, [status(thm)], [c_112])).
% 2.53/1.41  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_34])).
% 2.53/1.41  tff(c_136, plain, (![B_71]: (v1_xboole_0(k3_xboole_0(B_71, '#skF_4')))), inference(splitRight, [status(thm)], [c_112])).
% 2.53/1.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.41  tff(c_47, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2])).
% 2.53/1.41  tff(c_140, plain, (![B_71]: (k3_xboole_0(B_71, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_136, c_47])).
% 2.53/1.41  tff(c_165, plain, (![A_75, B_76]: (r1_tarski('#skF_2'(A_75, B_76), B_76) | v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.53/1.41  tff(c_176, plain, (![A_78]: (r1_tarski('#skF_2'(A_78, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_48, c_165])).
% 2.53/1.41  tff(c_4, plain, (![A_2, B_3]: (k3_xboole_0(A_2, B_3)=A_2 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.41  tff(c_179, plain, (![A_78]: (k3_xboole_0('#skF_2'(A_78, '#skF_4'), '#skF_4')='#skF_2'(A_78, '#skF_4') | v2_tex_2('#skF_4', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_176, c_4])).
% 2.53/1.41  tff(c_200, plain, (![A_81]: ('#skF_2'(A_81, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_81) | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_179])).
% 2.53/1.41  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.53/1.41  tff(c_203, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_200, c_30])).
% 2.53/1.41  tff(c_206, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_203])).
% 2.53/1.41  tff(c_113, plain, (![B_69, A_70]: (v4_pre_topc(B_69, A_70) | ~v1_xboole_0(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.41  tff(c_125, plain, (![A_70]: (v4_pre_topc('#skF_4', A_70) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(resolution, [status(thm)], [c_48, c_113])).
% 2.53/1.41  tff(c_130, plain, (![A_70]: (v4_pre_topc('#skF_4', A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_125])).
% 2.53/1.41  tff(c_143, plain, (![A_10, B_60]: (k9_subset_1(A_10, B_60, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_76])).
% 2.53/1.41  tff(c_387, plain, (![A_115, B_116, D_117]: (k9_subset_1(u1_struct_0(A_115), B_116, D_117)!='#skF_2'(A_115, B_116) | ~v4_pre_topc(D_117, A_115) | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0(A_115))) | v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.53/1.41  tff(c_393, plain, (![A_115, B_60]: ('#skF_2'(A_115, B_60)!='#skF_4' | ~v4_pre_topc('#skF_4', A_115) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_115))) | v2_tex_2(B_60, A_115) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(superposition, [status(thm), theory('equality')], [c_143, c_387])).
% 2.53/1.41  tff(c_396, plain, (![A_118, B_119]: ('#skF_2'(A_118, B_119)!='#skF_4' | ~v4_pre_topc('#skF_4', A_118) | v2_tex_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_393])).
% 2.53/1.41  tff(c_415, plain, (![A_120]: ('#skF_2'(A_120, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_120) | v2_tex_2('#skF_4', A_120) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_48, c_396])).
% 2.53/1.41  tff(c_420, plain, (![A_121]: ('#skF_2'(A_121, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(resolution, [status(thm)], [c_130, c_415])).
% 2.53/1.41  tff(c_423, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_420, c_30])).
% 2.53/1.41  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_206, c_423])).
% 2.53/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.41  
% 2.53/1.41  Inference rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Ref     : 0
% 2.53/1.41  #Sup     : 86
% 2.53/1.41  #Fact    : 0
% 2.53/1.41  #Define  : 0
% 2.53/1.41  #Split   : 1
% 2.53/1.41  #Chain   : 0
% 2.53/1.41  #Close   : 0
% 2.53/1.41  
% 2.53/1.41  Ordering : KBO
% 2.53/1.41  
% 2.53/1.41  Simplification rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Subsume      : 8
% 2.53/1.41  #Demod        : 57
% 2.53/1.41  #Tautology    : 33
% 2.53/1.41  #SimpNegUnit  : 4
% 2.53/1.41  #BackRed      : 6
% 2.53/1.41  
% 2.53/1.41  #Partial instantiations: 0
% 2.53/1.41  #Strategies tried      : 1
% 2.53/1.41  
% 2.53/1.41  Timing (in seconds)
% 2.53/1.41  ----------------------
% 2.53/1.41  Preprocessing        : 0.32
% 2.53/1.41  Parsing              : 0.17
% 2.53/1.41  CNF conversion       : 0.02
% 2.53/1.41  Main loop            : 0.30
% 2.53/1.41  Inferencing          : 0.11
% 2.53/1.41  Reduction            : 0.09
% 2.53/1.41  Demodulation         : 0.06
% 2.53/1.41  BG Simplification    : 0.02
% 2.53/1.41  Subsumption          : 0.06
% 2.53/1.41  Abstraction          : 0.02
% 2.53/1.41  MUC search           : 0.00
% 2.53/1.41  Cooper               : 0.00
% 2.53/1.41  Total                : 0.66
% 2.53/1.41  Index Insertion      : 0.00
% 2.53/1.41  Index Deletion       : 0.00
% 2.53/1.41  Index Matching       : 0.00
% 2.53/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
