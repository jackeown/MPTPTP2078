%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 361 expanded)
%              Number of equality atoms :   21 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_104,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_162,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2'(A_75,B_76),B_76)
      | v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_167,plain,(
    ! [A_77] :
      ( r1_tarski('#skF_2'(A_77,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_56,c_162])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_66,plain,(
    ! [B_52,A_53] :
      ( ~ r1_xboole_0(B_52,A_53)
      | ~ r1_tarski(B_52,A_53)
      | v1_xboole_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_4] :
      ( ~ r1_tarski(A_4,'#skF_4')
      | v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_172,plain,(
    ! [A_78] :
      ( v1_xboole_0('#skF_2'(A_78,'#skF_4'))
      | v2_tex_2('#skF_4',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_167,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_177,plain,(
    ! [A_79] :
      ( '#skF_2'(A_79,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_172,c_49])).

tff(c_180,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_32])).

tff(c_183,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_180])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_117,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tops_1(A_67,B_68),B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    ! [A_69] :
      ( r1_tarski(k1_tops_1(A_69,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_56,c_117])).

tff(c_127,plain,(
    ! [A_70] :
      ( v1_xboole_0(k1_tops_1(A_70,'#skF_4'))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_122,c_70])).

tff(c_137,plain,(
    ! [A_73] :
      ( k1_tops_1(A_73,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_127,c_49])).

tff(c_141,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_132,plain,(
    ! [A_71,B_72] :
      ( v3_pre_topc(k1_tops_1(A_71,B_72),A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_156,plain,(
    ! [A_74] :
      ( v3_pre_topc(k1_tops_1(A_74,'#skF_4'),A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_159,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_156])).

tff(c_161,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_159])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k3_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_54] :
      ( ~ r1_tarski(A_54,'#skF_4')
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_81,plain,(
    ! [B_58] : v1_xboole_0(k3_xboole_0('#skF_4',B_58)) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_85,plain,(
    ! [B_58] : k3_xboole_0('#skF_4',B_58) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_81,c_49])).

tff(c_103,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_10,B_61] : k9_subset_1(A_10,B_61,'#skF_4') = k3_xboole_0(B_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_303,plain,(
    ! [A_102,B_103,D_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,D_104) != '#skF_2'(A_102,B_103)
      | ~ v3_pre_topc(D_104,A_102)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_308,plain,(
    ! [B_61,A_102] :
      ( k3_xboole_0(B_61,'#skF_4') != '#skF_2'(A_102,B_61)
      | ~ v3_pre_topc('#skF_4',A_102)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_102)))
      | v2_tex_2(B_61,A_102)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_303])).

tff(c_311,plain,(
    ! [B_105,A_106] :
      ( k3_xboole_0(B_105,'#skF_4') != '#skF_2'(A_106,B_105)
      | ~ v3_pre_topc('#skF_4',A_106)
      | v2_tex_2(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_308])).

tff(c_318,plain,(
    ! [A_106] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_106,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_106)
      | v2_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_56,c_311])).

tff(c_322,plain,(
    ! [A_107] :
      ( '#skF_2'(A_107,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_107)
      | v2_tex_2('#skF_4',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_318])).

tff(c_325,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_322])).

tff(c_328,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183,c_325])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.30/1.29  
% 2.30/1.29  %Foreground sorts:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Background operators:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Foreground operators:
% 2.30/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.29  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.30/1.29  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.30/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.30/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.30/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.29  
% 2.30/1.30  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.30/1.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.30/1.30  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.30/1.30  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.30/1.30  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.30/1.30  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.30/1.30  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.30/1.30  tff(f_61, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.30/1.30  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.30/1.30  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.30/1.30  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.30  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.30  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.30  tff(c_44, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.30  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.30/1.30  tff(c_12, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.30  tff(c_56, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.30/1.30  tff(c_162, plain, (![A_75, B_76]: (r1_tarski('#skF_2'(A_75, B_76), B_76) | v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.30  tff(c_167, plain, (![A_77]: (r1_tarski('#skF_2'(A_77, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_56, c_162])).
% 2.30/1.30  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.30  tff(c_50, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 2.30/1.30  tff(c_66, plain, (![B_52, A_53]: (~r1_xboole_0(B_52, A_53) | ~r1_tarski(B_52, A_53) | v1_xboole_0(B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.30  tff(c_70, plain, (![A_4]: (~r1_tarski(A_4, '#skF_4') | v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_50, c_66])).
% 2.30/1.30  tff(c_172, plain, (![A_78]: (v1_xboole_0('#skF_2'(A_78, '#skF_4')) | v2_tex_2('#skF_4', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_167, c_70])).
% 2.30/1.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.30  tff(c_49, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2])).
% 2.30/1.30  tff(c_177, plain, (![A_79]: ('#skF_2'(A_79, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_172, c_49])).
% 2.30/1.30  tff(c_180, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_177, c_32])).
% 2.30/1.30  tff(c_183, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_180])).
% 2.30/1.30  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.30/1.30  tff(c_117, plain, (![A_67, B_68]: (r1_tarski(k1_tops_1(A_67, B_68), B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.30  tff(c_122, plain, (![A_69]: (r1_tarski(k1_tops_1(A_69, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_56, c_117])).
% 2.30/1.30  tff(c_127, plain, (![A_70]: (v1_xboole_0(k1_tops_1(A_70, '#skF_4')) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_122, c_70])).
% 2.30/1.30  tff(c_137, plain, (![A_73]: (k1_tops_1(A_73, '#skF_4')='#skF_4' | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_127, c_49])).
% 2.30/1.30  tff(c_141, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_137])).
% 2.30/1.30  tff(c_132, plain, (![A_71, B_72]: (v3_pre_topc(k1_tops_1(A_71, B_72), A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.30  tff(c_156, plain, (![A_74]: (v3_pre_topc(k1_tops_1(A_74, '#skF_4'), A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(resolution, [status(thm)], [c_56, c_132])).
% 2.30/1.30  tff(c_159, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_156])).
% 2.30/1.30  tff(c_161, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_159])).
% 2.30/1.30  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k3_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.30  tff(c_71, plain, (![A_54]: (~r1_tarski(A_54, '#skF_4') | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_50, c_66])).
% 2.30/1.30  tff(c_81, plain, (![B_58]: (v1_xboole_0(k3_xboole_0('#skF_4', B_58)))), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.30/1.30  tff(c_85, plain, (![B_58]: (k3_xboole_0('#skF_4', B_58)='#skF_4')), inference(resolution, [status(thm)], [c_81, c_49])).
% 2.30/1.30  tff(c_103, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.30/1.30  tff(c_106, plain, (![A_10, B_61]: (k9_subset_1(A_10, B_61, '#skF_4')=k3_xboole_0(B_61, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_103])).
% 2.30/1.30  tff(c_303, plain, (![A_102, B_103, D_104]: (k9_subset_1(u1_struct_0(A_102), B_103, D_104)!='#skF_2'(A_102, B_103) | ~v3_pre_topc(D_104, A_102) | ~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(A_102))) | v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.30  tff(c_308, plain, (![B_61, A_102]: (k3_xboole_0(B_61, '#skF_4')!='#skF_2'(A_102, B_61) | ~v3_pre_topc('#skF_4', A_102) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_102))) | v2_tex_2(B_61, A_102) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_106, c_303])).
% 2.30/1.30  tff(c_311, plain, (![B_105, A_106]: (k3_xboole_0(B_105, '#skF_4')!='#skF_2'(A_106, B_105) | ~v3_pre_topc('#skF_4', A_106) | v2_tex_2(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_308])).
% 2.30/1.30  tff(c_318, plain, (![A_106]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_106, '#skF_4') | ~v3_pre_topc('#skF_4', A_106) | v2_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_56, c_311])).
% 2.30/1.30  tff(c_322, plain, (![A_107]: ('#skF_2'(A_107, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_107) | v2_tex_2('#skF_4', A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_318])).
% 2.30/1.30  tff(c_325, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_161, c_322])).
% 2.30/1.30  tff(c_328, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_183, c_325])).
% 2.30/1.30  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_328])).
% 2.30/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.30  
% 2.30/1.30  Inference rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Ref     : 0
% 2.30/1.30  #Sup     : 59
% 2.30/1.30  #Fact    : 0
% 2.30/1.30  #Define  : 0
% 2.30/1.30  #Split   : 0
% 2.30/1.30  #Chain   : 0
% 2.30/1.30  #Close   : 0
% 2.30/1.30  
% 2.30/1.30  Ordering : KBO
% 2.30/1.30  
% 2.30/1.30  Simplification rules
% 2.30/1.30  ----------------------
% 2.30/1.30  #Subsume      : 1
% 2.30/1.30  #Demod        : 58
% 2.30/1.30  #Tautology    : 27
% 2.30/1.30  #SimpNegUnit  : 11
% 2.30/1.30  #BackRed      : 3
% 2.30/1.30  
% 2.30/1.30  #Partial instantiations: 0
% 2.30/1.30  #Strategies tried      : 1
% 2.30/1.30  
% 2.30/1.30  Timing (in seconds)
% 2.30/1.30  ----------------------
% 2.30/1.31  Preprocessing        : 0.31
% 2.30/1.31  Parsing              : 0.17
% 2.30/1.31  CNF conversion       : 0.02
% 2.30/1.31  Main loop            : 0.22
% 2.30/1.31  Inferencing          : 0.09
% 2.30/1.31  Reduction            : 0.07
% 2.30/1.31  Demodulation         : 0.05
% 2.30/1.31  BG Simplification    : 0.01
% 2.30/1.31  Subsumption          : 0.04
% 2.30/1.31  Abstraction          : 0.02
% 2.30/1.31  MUC search           : 0.00
% 2.30/1.31  Cooper               : 0.00
% 2.30/1.31  Total                : 0.56
% 2.30/1.31  Index Insertion      : 0.00
% 2.30/1.31  Index Deletion       : 0.00
% 2.30/1.31  Index Matching       : 0.00
% 2.30/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
