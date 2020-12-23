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
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 158 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 325 expanded)
%              Number of equality atoms :   26 (  65 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

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
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_323,plain,(
    ! [A_81,B_82] :
      ( r1_tarski('#skF_2'(A_81,B_82),B_82)
      | v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_328,plain,(
    ! [A_83] :
      ( r1_tarski('#skF_2'(A_83,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_50,c_323])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_6])).

tff(c_333,plain,(
    ! [A_84] :
      ( '#skF_2'(A_84,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_328,c_64])).

tff(c_336,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_32])).

tff(c_339,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_336])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_176,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_190,plain,(
    ! [A_72] :
      ( r1_tarski(k1_tops_1(A_72,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_50,c_176])).

tff(c_195,plain,(
    ! [A_73] :
      ( k1_tops_1(A_73,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_190,c_64])).

tff(c_199,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_265,plain,(
    ! [A_76,B_77] :
      ( v3_pre_topc(k1_tops_1(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_270,plain,(
    ! [A_78] :
      ( v3_pre_topc(k1_tops_1(A_78,'#skF_4'),A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_50,c_265])).

tff(c_273,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_270])).

tff(c_275,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_273])).

tff(c_86,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_51] :
      ( A_51 = '#skF_4'
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_6])).

tff(c_70,plain,(
    ! [B_3] : k4_xboole_0('#skF_4',B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_96,plain,(
    ! [B_54] : k3_xboole_0('#skF_4',B_54) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_70])).

tff(c_172,plain,(
    ! [A_65,B_66,C_67] :
      ( k9_subset_1(A_65,B_66,C_67) = k3_xboole_0(B_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_175,plain,(
    ! [A_10,B_66] : k9_subset_1(A_10,B_66,'#skF_4') = k3_xboole_0(B_66,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_172])).

tff(c_689,plain,(
    ! [A_109,B_110,D_111] :
      ( k9_subset_1(u1_struct_0(A_109),B_110,D_111) != '#skF_2'(A_109,B_110)
      | ~ v3_pre_topc(D_111,A_109)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_692,plain,(
    ! [B_66,A_109] :
      ( k3_xboole_0(B_66,'#skF_4') != '#skF_2'(A_109,B_66)
      | ~ v3_pre_topc('#skF_4',A_109)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_109)))
      | v2_tex_2(B_66,A_109)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_689])).

tff(c_695,plain,(
    ! [B_112,A_113] :
      ( k3_xboole_0(B_112,'#skF_4') != '#skF_2'(A_113,B_112)
      | ~ v3_pre_topc('#skF_4',A_113)
      | v2_tex_2(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_692])).

tff(c_705,plain,(
    ! [A_113] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_113,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_113)
      | v2_tex_2('#skF_4',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_50,c_695])).

tff(c_710,plain,(
    ! [A_114] :
      ( '#skF_2'(A_114,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_114)
      | v2_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_705])).

tff(c_713,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_710])).

tff(c_716,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_339,c_713])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.81/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.81/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.81/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.40  
% 2.81/1.42  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.81/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.81/1.42  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.42  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.81/1.42  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.81/1.42  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.81/1.42  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.81/1.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.42  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.81/1.42  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.81/1.42  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.42  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.42  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.42  tff(c_44, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.42  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.81/1.42  tff(c_12, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.42  tff(c_50, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.81/1.42  tff(c_323, plain, (![A_81, B_82]: (r1_tarski('#skF_2'(A_81, B_82), B_82) | v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_328, plain, (![A_83]: (r1_tarski('#skF_2'(A_83, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_50, c_323])).
% 2.81/1.42  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.42  tff(c_64, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.81/1.42  tff(c_333, plain, (![A_84]: ('#skF_2'(A_84, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_328, c_64])).
% 2.81/1.42  tff(c_336, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_333, c_32])).
% 2.81/1.42  tff(c_339, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_336])).
% 2.81/1.42  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.42  tff(c_176, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.42  tff(c_190, plain, (![A_72]: (r1_tarski(k1_tops_1(A_72, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_50, c_176])).
% 2.81/1.42  tff(c_195, plain, (![A_73]: (k1_tops_1(A_73, '#skF_4')='#skF_4' | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_190, c_64])).
% 2.81/1.42  tff(c_199, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_195])).
% 2.81/1.42  tff(c_265, plain, (![A_76, B_77]: (v3_pre_topc(k1_tops_1(A_76, B_77), A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.42  tff(c_270, plain, (![A_78]: (v3_pre_topc(k1_tops_1(A_78, '#skF_4'), A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(resolution, [status(thm)], [c_50, c_265])).
% 2.81/1.42  tff(c_273, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_270])).
% 2.81/1.42  tff(c_275, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_273])).
% 2.81/1.42  tff(c_86, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.42  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.42  tff(c_65, plain, (![A_51]: (A_51='#skF_4' | ~r1_tarski(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.81/1.42  tff(c_70, plain, (![B_3]: (k4_xboole_0('#skF_4', B_3)='#skF_4')), inference(resolution, [status(thm)], [c_4, c_65])).
% 2.81/1.42  tff(c_96, plain, (![B_54]: (k3_xboole_0('#skF_4', B_54)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_86, c_70])).
% 2.81/1.42  tff(c_172, plain, (![A_65, B_66, C_67]: (k9_subset_1(A_65, B_66, C_67)=k3_xboole_0(B_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.42  tff(c_175, plain, (![A_10, B_66]: (k9_subset_1(A_10, B_66, '#skF_4')=k3_xboole_0(B_66, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_172])).
% 2.81/1.42  tff(c_689, plain, (![A_109, B_110, D_111]: (k9_subset_1(u1_struct_0(A_109), B_110, D_111)!='#skF_2'(A_109, B_110) | ~v3_pre_topc(D_111, A_109) | ~m1_subset_1(D_111, k1_zfmisc_1(u1_struct_0(A_109))) | v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_692, plain, (![B_66, A_109]: (k3_xboole_0(B_66, '#skF_4')!='#skF_2'(A_109, B_66) | ~v3_pre_topc('#skF_4', A_109) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_109))) | v2_tex_2(B_66, A_109) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_175, c_689])).
% 2.81/1.42  tff(c_695, plain, (![B_112, A_113]: (k3_xboole_0(B_112, '#skF_4')!='#skF_2'(A_113, B_112) | ~v3_pre_topc('#skF_4', A_113) | v2_tex_2(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_692])).
% 2.81/1.42  tff(c_705, plain, (![A_113]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_113, '#skF_4') | ~v3_pre_topc('#skF_4', A_113) | v2_tex_2('#skF_4', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_50, c_695])).
% 2.81/1.42  tff(c_710, plain, (![A_114]: ('#skF_2'(A_114, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_114) | v2_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_705])).
% 2.81/1.42  tff(c_713, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_275, c_710])).
% 2.81/1.42  tff(c_716, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_339, c_713])).
% 2.81/1.42  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_716])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 158
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 0
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 1
% 2.81/1.42  #Demod        : 182
% 2.81/1.42  #Tautology    : 96
% 2.81/1.42  #SimpNegUnit  : 7
% 2.81/1.42  #BackRed      : 2
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.32
% 2.81/1.42  Parsing              : 0.17
% 2.81/1.42  CNF conversion       : 0.02
% 2.81/1.42  Main loop            : 0.32
% 2.81/1.42  Inferencing          : 0.12
% 2.81/1.42  Reduction            : 0.11
% 2.81/1.42  Demodulation         : 0.09
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.04
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.68
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
