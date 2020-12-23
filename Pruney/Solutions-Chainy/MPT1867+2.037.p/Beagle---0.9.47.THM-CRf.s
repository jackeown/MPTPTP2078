%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 198 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 450 expanded)
%              Number of equality atoms :   26 (  78 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_165,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2'(A_75,B_76),B_76)
      | v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_170,plain,(
    ! [A_77] :
      ( r1_tarski('#skF_2'(A_77,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_72,c_165])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_83,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ r1_tarski(A_5,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_73,c_83])).

tff(c_197,plain,(
    ! [A_80] :
      ( '#skF_2'(A_80,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_170,c_88])).

tff(c_200,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_38])).

tff(c_203,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_200])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_180,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_2'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( v4_pre_topc(B_18,A_16)
      | ~ v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_226,plain,(
    ! [A_84,B_85] :
      ( v4_pre_topc('#skF_2'(A_84,B_85),A_84)
      | ~ v1_xboole_0('#skF_2'(A_84,B_85))
      | ~ v2_pre_topc(A_84)
      | v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_180,c_24])).

tff(c_244,plain,(
    ! [A_89] :
      ( v4_pre_topc('#skF_2'(A_89,'#skF_4'),A_89)
      | ~ v1_xboole_0('#skF_2'(A_89,'#skF_4'))
      | ~ v2_pre_topc(A_89)
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_72,c_226])).

tff(c_247,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_244])).

tff(c_249,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_203,c_247])).

tff(c_250,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_249])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [A_4] : k3_xboole_0(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_12])).

tff(c_124,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [A_12,B_63] : k9_subset_1(A_12,B_63,'#skF_4') = k3_xboole_0(B_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_128,plain,(
    ! [A_12,B_63] : k9_subset_1(A_12,B_63,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_126])).

tff(c_136,plain,(
    ! [A_67,C_68,B_69] :
      ( k9_subset_1(A_67,C_68,B_69) = k9_subset_1(A_67,B_69,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [A_12,B_69] : k9_subset_1(A_12,B_69,'#skF_4') = k9_subset_1(A_12,'#skF_4',B_69) ),
    inference(resolution,[status(thm)],[c_72,c_136])).

tff(c_140,plain,(
    ! [A_12,B_69] : k9_subset_1(A_12,'#skF_4',B_69) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_138])).

tff(c_335,plain,(
    ! [A_102,B_103,D_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,D_104) != '#skF_2'(A_102,B_103)
      | ~ v4_pre_topc(D_104,A_102)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_340,plain,(
    ! [A_102,B_69] :
      ( '#skF_2'(A_102,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_69,A_102)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_102)))
      | v2_tex_2('#skF_4',A_102)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_335])).

tff(c_348,plain,(
    ! [A_105,B_106] :
      ( '#skF_2'(A_105,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2('#skF_4',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_340])).

tff(c_362,plain,(
    ! [A_107] :
      ( '#skF_2'(A_107,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_107)
      | v2_tex_2('#skF_4',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_72,c_348])).

tff(c_365,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_362])).

tff(c_371,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_203,c_365])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.28  
% 2.41/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.28  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.41/1.28  
% 2.41/1.28  %Foreground sorts:
% 2.41/1.28  
% 2.41/1.28  
% 2.41/1.28  %Background operators:
% 2.41/1.28  
% 2.41/1.28  
% 2.41/1.28  %Foreground operators:
% 2.41/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.41/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.41/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.28  
% 2.41/1.30  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.41/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.41/1.30  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.41/1.30  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.41/1.30  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.41/1.30  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.30  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.41/1.30  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.41/1.30  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.41/1.30  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.41/1.30  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.41/1.30  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.41/1.30  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.41/1.30  tff(c_60, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.41/1.30  tff(c_69, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_60])).
% 2.41/1.30  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.30  tff(c_72, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_20])).
% 2.41/1.30  tff(c_165, plain, (![A_75, B_76]: (r1_tarski('#skF_2'(A_75, B_76), B_76) | v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.30  tff(c_170, plain, (![A_77]: (r1_tarski('#skF_2'(A_77, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_72, c_165])).
% 2.41/1.30  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.30  tff(c_73, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 2.41/1.30  tff(c_83, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.41/1.30  tff(c_88, plain, (![A_5]: (A_5='#skF_4' | ~r1_tarski(A_5, '#skF_4'))), inference(resolution, [status(thm)], [c_73, c_83])).
% 2.41/1.30  tff(c_197, plain, (![A_80]: ('#skF_2'(A_80, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_170, c_88])).
% 2.41/1.30  tff(c_200, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_197, c_38])).
% 2.41/1.30  tff(c_203, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_200])).
% 2.41/1.30  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.41/1.30  tff(c_180, plain, (![A_78, B_79]: (m1_subset_1('#skF_2'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.30  tff(c_24, plain, (![B_18, A_16]: (v4_pre_topc(B_18, A_16) | ~v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.41/1.30  tff(c_226, plain, (![A_84, B_85]: (v4_pre_topc('#skF_2'(A_84, B_85), A_84) | ~v1_xboole_0('#skF_2'(A_84, B_85)) | ~v2_pre_topc(A_84) | v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_180, c_24])).
% 2.41/1.30  tff(c_244, plain, (![A_89]: (v4_pre_topc('#skF_2'(A_89, '#skF_4'), A_89) | ~v1_xboole_0('#skF_2'(A_89, '#skF_4')) | ~v2_pre_topc(A_89) | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_72, c_226])).
% 2.41/1.30  tff(c_247, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_203, c_244])).
% 2.41/1.30  tff(c_249, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_203, c_247])).
% 2.41/1.30  tff(c_250, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_249])).
% 2.41/1.30  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.41/1.30  tff(c_71, plain, (![A_4]: (k3_xboole_0(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_12])).
% 2.41/1.30  tff(c_124, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.30  tff(c_126, plain, (![A_12, B_63]: (k9_subset_1(A_12, B_63, '#skF_4')=k3_xboole_0(B_63, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_124])).
% 2.41/1.30  tff(c_128, plain, (![A_12, B_63]: (k9_subset_1(A_12, B_63, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_126])).
% 2.41/1.30  tff(c_136, plain, (![A_67, C_68, B_69]: (k9_subset_1(A_67, C_68, B_69)=k9_subset_1(A_67, B_69, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.30  tff(c_138, plain, (![A_12, B_69]: (k9_subset_1(A_12, B_69, '#skF_4')=k9_subset_1(A_12, '#skF_4', B_69))), inference(resolution, [status(thm)], [c_72, c_136])).
% 2.41/1.30  tff(c_140, plain, (![A_12, B_69]: (k9_subset_1(A_12, '#skF_4', B_69)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_138])).
% 2.41/1.30  tff(c_335, plain, (![A_102, B_103, D_104]: (k9_subset_1(u1_struct_0(A_102), B_103, D_104)!='#skF_2'(A_102, B_103) | ~v4_pre_topc(D_104, A_102) | ~m1_subset_1(D_104, k1_zfmisc_1(u1_struct_0(A_102))) | v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.30  tff(c_340, plain, (![A_102, B_69]: ('#skF_2'(A_102, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_69, A_102) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_102))) | v2_tex_2('#skF_4', A_102) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_140, c_335])).
% 2.41/1.30  tff(c_348, plain, (![A_105, B_106]: ('#skF_2'(A_105, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2('#skF_4', A_105) | ~l1_pre_topc(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_340])).
% 2.41/1.30  tff(c_362, plain, (![A_107]: ('#skF_2'(A_107, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_107) | v2_tex_2('#skF_4', A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_72, c_348])).
% 2.41/1.30  tff(c_365, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_362])).
% 2.41/1.30  tff(c_371, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_203, c_365])).
% 2.41/1.30  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_371])).
% 2.41/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.30  
% 2.41/1.30  Inference rules
% 2.41/1.30  ----------------------
% 2.41/1.30  #Ref     : 0
% 2.41/1.30  #Sup     : 71
% 2.41/1.30  #Fact    : 0
% 2.41/1.30  #Define  : 0
% 2.41/1.30  #Split   : 0
% 2.41/1.30  #Chain   : 0
% 2.41/1.30  #Close   : 0
% 2.41/1.30  
% 2.41/1.30  Ordering : KBO
% 2.41/1.30  
% 2.41/1.30  Simplification rules
% 2.41/1.30  ----------------------
% 2.41/1.30  #Subsume      : 4
% 2.41/1.30  #Demod        : 37
% 2.41/1.30  #Tautology    : 30
% 2.41/1.30  #SimpNegUnit  : 7
% 2.41/1.30  #BackRed      : 5
% 2.41/1.30  
% 2.41/1.30  #Partial instantiations: 0
% 2.41/1.30  #Strategies tried      : 1
% 2.41/1.30  
% 2.41/1.30  Timing (in seconds)
% 2.41/1.30  ----------------------
% 2.41/1.30  Preprocessing        : 0.32
% 2.41/1.30  Parsing              : 0.16
% 2.41/1.30  CNF conversion       : 0.02
% 2.41/1.30  Main loop            : 0.23
% 2.41/1.30  Inferencing          : 0.08
% 2.41/1.30  Reduction            : 0.07
% 2.41/1.30  Demodulation         : 0.05
% 2.41/1.30  BG Simplification    : 0.02
% 2.41/1.30  Subsumption          : 0.05
% 2.41/1.30  Abstraction          : 0.02
% 2.41/1.30  MUC search           : 0.00
% 2.41/1.30  Cooper               : 0.00
% 2.41/1.30  Total                : 0.58
% 2.41/1.30  Index Insertion      : 0.00
% 2.41/1.30  Index Deletion       : 0.00
% 2.41/1.30  Index Matching       : 0.00
% 2.41/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
