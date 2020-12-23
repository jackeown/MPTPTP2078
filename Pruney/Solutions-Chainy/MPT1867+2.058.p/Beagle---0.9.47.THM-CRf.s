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
% DateTime   : Thu Dec  3 10:29:30 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 148 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  111 ( 306 expanded)
%              Number of equality atoms :   22 (  58 expanded)
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

tff(f_100,negated_conjecture,(
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

tff(f_85,axiom,(
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
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_10,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_189,plain,(
    ! [A_83,B_84] :
      ( r1_tarski('#skF_2'(A_83,B_84),B_84)
      | v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_240,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_2'(A_92,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_50,c_189])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ r1_tarski(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_4])).

tff(c_251,plain,(
    ! [A_93] :
      ( '#skF_2'(A_93,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_240,c_63])).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_254,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_251,c_32])).

tff(c_257,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_254])).

tff(c_164,plain,(
    ! [B_77,A_78] :
      ( v4_pre_topc(B_77,A_78)
      | ~ v1_xboole_0(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_176,plain,(
    ! [A_78] :
      ( v4_pre_topc('#skF_4',A_78)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_50,c_164])).

tff(c_181,plain,(
    ! [A_78] :
      ( v4_pre_topc('#skF_4',A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_176])).

tff(c_91,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_68,B_69] : k9_subset_1(A_68,B_69,'#skF_4') = k3_xboole_0(B_69,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_91])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_69,A_68] :
      ( m1_subset_1(k3_xboole_0(B_69,'#skF_4'),k1_zfmisc_1(A_68))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_6])).

tff(c_123,plain,(
    ! [B_70,A_71] : m1_subset_1(k3_xboole_0(B_70,'#skF_4'),k1_zfmisc_1(A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_115])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [B_72,A_73] : r1_tarski(k3_xboole_0(B_72,'#skF_4'),A_73) ),
    inference(resolution,[status(thm)],[c_123,c_12])).

tff(c_139,plain,(
    ! [B_72] : k3_xboole_0(B_72,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_134,c_63])).

tff(c_97,plain,(
    ! [A_9,B_63] : k9_subset_1(A_9,B_63,'#skF_4') = k3_xboole_0(B_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_91])).

tff(c_142,plain,(
    ! [A_9,B_63] : k9_subset_1(A_9,B_63,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_97])).

tff(c_538,plain,(
    ! [A_124,B_125,D_126] :
      ( k9_subset_1(u1_struct_0(A_124),B_125,D_126) != '#skF_2'(A_124,B_125)
      | ~ v4_pre_topc(D_126,A_124)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_124)))
      | v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_541,plain,(
    ! [A_124,B_63] :
      ( '#skF_2'(A_124,B_63) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_124)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_124)))
      | v2_tex_2(B_63,A_124)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_538])).

tff(c_840,plain,(
    ! [A_157,B_158] :
      ( '#skF_2'(A_157,B_158) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_157)
      | v2_tex_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_541])).

tff(c_883,plain,(
    ! [A_161] :
      ( '#skF_2'(A_161,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_161)
      | v2_tex_2('#skF_4',A_161)
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_50,c_840])).

tff(c_888,plain,(
    ! [A_162] :
      ( '#skF_2'(A_162,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_181,c_883])).

tff(c_891,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_888,c_32])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_257,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.46  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.76/1.46  
% 2.76/1.46  %Foreground sorts:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Background operators:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Foreground operators:
% 2.76/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.76/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.76/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.46  
% 3.17/1.47  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.17/1.47  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.17/1.47  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.17/1.47  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.17/1.47  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.17/1.47  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.17/1.47  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.17/1.47  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.17/1.47  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.47  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.47  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.47  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.47  tff(c_44, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.47  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 3.17/1.47  tff(c_10, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.47  tff(c_50, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 3.17/1.47  tff(c_189, plain, (![A_83, B_84]: (r1_tarski('#skF_2'(A_83, B_84), B_84) | v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_240, plain, (![A_92]: (r1_tarski('#skF_2'(A_92, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_50, c_189])).
% 3.17/1.47  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.47  tff(c_63, plain, (![A_2]: (A_2='#skF_4' | ~r1_tarski(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_4])).
% 3.17/1.47  tff(c_251, plain, (![A_93]: ('#skF_2'(A_93, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_240, c_63])).
% 3.17/1.47  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.47  tff(c_254, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_251, c_32])).
% 3.17/1.47  tff(c_257, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_254])).
% 3.17/1.47  tff(c_164, plain, (![B_77, A_78]: (v4_pre_topc(B_77, A_78) | ~v1_xboole_0(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.17/1.47  tff(c_176, plain, (![A_78]: (v4_pre_topc('#skF_4', A_78) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(resolution, [status(thm)], [c_50, c_164])).
% 3.17/1.47  tff(c_181, plain, (![A_78]: (v4_pre_topc('#skF_4', A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_176])).
% 3.17/1.47  tff(c_91, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.47  tff(c_109, plain, (![A_68, B_69]: (k9_subset_1(A_68, B_69, '#skF_4')=k3_xboole_0(B_69, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_91])).
% 3.17/1.47  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.47  tff(c_115, plain, (![B_69, A_68]: (m1_subset_1(k3_xboole_0(B_69, '#skF_4'), k1_zfmisc_1(A_68)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_6])).
% 3.17/1.47  tff(c_123, plain, (![B_70, A_71]: (m1_subset_1(k3_xboole_0(B_70, '#skF_4'), k1_zfmisc_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_115])).
% 3.17/1.47  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.47  tff(c_134, plain, (![B_72, A_73]: (r1_tarski(k3_xboole_0(B_72, '#skF_4'), A_73))), inference(resolution, [status(thm)], [c_123, c_12])).
% 3.17/1.47  tff(c_139, plain, (![B_72]: (k3_xboole_0(B_72, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_134, c_63])).
% 3.17/1.47  tff(c_97, plain, (![A_9, B_63]: (k9_subset_1(A_9, B_63, '#skF_4')=k3_xboole_0(B_63, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_91])).
% 3.17/1.47  tff(c_142, plain, (![A_9, B_63]: (k9_subset_1(A_9, B_63, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_97])).
% 3.17/1.47  tff(c_538, plain, (![A_124, B_125, D_126]: (k9_subset_1(u1_struct_0(A_124), B_125, D_126)!='#skF_2'(A_124, B_125) | ~v4_pre_topc(D_126, A_124) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(A_124))) | v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.47  tff(c_541, plain, (![A_124, B_63]: ('#skF_2'(A_124, B_63)!='#skF_4' | ~v4_pre_topc('#skF_4', A_124) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_124))) | v2_tex_2(B_63, A_124) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_142, c_538])).
% 3.17/1.47  tff(c_840, plain, (![A_157, B_158]: ('#skF_2'(A_157, B_158)!='#skF_4' | ~v4_pre_topc('#skF_4', A_157) | v2_tex_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_541])).
% 3.17/1.47  tff(c_883, plain, (![A_161]: ('#skF_2'(A_161, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_161) | v2_tex_2('#skF_4', A_161) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_50, c_840])).
% 3.17/1.47  tff(c_888, plain, (![A_162]: ('#skF_2'(A_162, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162))), inference(resolution, [status(thm)], [c_181, c_883])).
% 3.17/1.47  tff(c_891, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_888, c_32])).
% 3.17/1.47  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_257, c_891])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 197
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.47  #Split   : 0
% 3.17/1.47  #Chain   : 0
% 3.17/1.47  #Close   : 0
% 3.17/1.47  
% 3.17/1.47  Ordering : KBO
% 3.17/1.47  
% 3.17/1.47  Simplification rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Subsume      : 15
% 3.17/1.47  #Demod        : 125
% 3.17/1.47  #Tautology    : 85
% 3.17/1.47  #SimpNegUnit  : 8
% 3.17/1.47  #BackRed      : 5
% 3.17/1.47  
% 3.17/1.47  #Partial instantiations: 0
% 3.17/1.47  #Strategies tried      : 1
% 3.17/1.47  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.48  Preprocessing        : 0.32
% 3.17/1.48  Parsing              : 0.17
% 3.17/1.48  CNF conversion       : 0.02
% 3.17/1.48  Main loop            : 0.37
% 3.17/1.48  Inferencing          : 0.14
% 3.17/1.48  Reduction            : 0.11
% 3.17/1.48  Demodulation         : 0.08
% 3.17/1.48  BG Simplification    : 0.02
% 3.17/1.48  Subsumption          : 0.07
% 3.17/1.48  Abstraction          : 0.02
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.72
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
