%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 135 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 260 expanded)
%              Number of equality atoms :   31 (  53 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_20] :
      ( v4_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_205,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_2'(A_80,B_81),B_81)
      | v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_259,plain,(
    ! [A_84] :
      ( r1_tarski('#skF_2'(A_84,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_80,c_205])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_6])).

tff(c_264,plain,(
    ! [A_85] :
      ( '#skF_2'(A_85,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_259,c_90])).

tff(c_267,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_264,c_40])).

tff(c_270,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_267])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_97,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_101,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_4,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_2] : k3_xboole_0(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_4])).

tff(c_125,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    ! [A_12,B_68] : k9_subset_1(A_12,B_68,'#skF_4') = k3_xboole_0(B_68,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_125])).

tff(c_132,plain,(
    ! [A_12,B_68] : k9_subset_1(A_12,B_68,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_129])).

tff(c_140,plain,(
    ! [A_72,C_73,B_74] :
      ( k9_subset_1(A_72,C_73,B_74) = k9_subset_1(A_72,B_74,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_12,B_74] : k9_subset_1(A_12,B_74,'#skF_4') = k9_subset_1(A_12,'#skF_4',B_74) ),
    inference(resolution,[status(thm)],[c_80,c_140])).

tff(c_147,plain,(
    ! [A_12,B_74] : k9_subset_1(A_12,'#skF_4',B_74) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_144])).

tff(c_621,plain,(
    ! [A_123,B_124,D_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,D_125) != '#skF_2'(A_123,B_124)
      | ~ v4_pre_topc(D_125,A_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_634,plain,(
    ! [A_123,B_74] :
      ( '#skF_2'(A_123,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_74,A_123)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2('#skF_4',A_123)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_621])).

tff(c_650,plain,(
    ! [A_126,B_127] :
      ( '#skF_2'(A_126,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2('#skF_4',A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_634])).

tff(c_659,plain,(
    ! [B_127] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_127,'#skF_3')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_650])).

tff(c_671,plain,(
    ! [B_127] :
      ( ~ v4_pre_topc(B_127,'#skF_3')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_270,c_659])).

tff(c_675,plain,(
    ! [B_128] :
      ( ~ v4_pre_topc(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_671])).

tff(c_688,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_675])).

tff(c_692,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_688])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n007.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 12:20:06 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.34  
% 2.74/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.34  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.74/1.34  
% 2.74/1.34  %Foreground sorts:
% 2.74/1.34  
% 2.74/1.34  
% 2.74/1.34  %Background operators:
% 2.74/1.34  
% 2.74/1.34  
% 2.74/1.34  %Foreground operators:
% 2.74/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.74/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.74/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.74/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.74/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.74/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.74/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.74/1.34  
% 2.74/1.36  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.74/1.36  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.74/1.36  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.74/1.36  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.74/1.36  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.74/1.36  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.74/1.36  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.74/1.36  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.74/1.36  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.74/1.36  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.74/1.36  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.74/1.36  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.74/1.36  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.74/1.36  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.36  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.36  tff(c_26, plain, (![A_20]: (v4_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.36  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.36  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.74/1.36  tff(c_51, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.74/1.36  tff(c_40, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.36  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.74/1.36  tff(c_62, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.36  tff(c_66, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_62])).
% 2.74/1.36  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.36  tff(c_80, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 2.74/1.36  tff(c_205, plain, (![A_80, B_81]: (r1_tarski('#skF_2'(A_80, B_81), B_81) | v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.74/1.36  tff(c_259, plain, (![A_84]: (r1_tarski('#skF_2'(A_84, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_80, c_205])).
% 2.74/1.36  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.36  tff(c_90, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_6])).
% 2.74/1.36  tff(c_264, plain, (![A_85]: ('#skF_2'(A_85, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_259, c_90])).
% 2.74/1.36  tff(c_267, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_264, c_40])).
% 2.74/1.36  tff(c_270, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_267])).
% 2.74/1.36  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.36  tff(c_92, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.36  tff(c_97, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_24, c_92])).
% 2.74/1.36  tff(c_101, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_97])).
% 2.74/1.36  tff(c_4, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.36  tff(c_72, plain, (![A_2]: (k3_xboole_0(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_4])).
% 2.74/1.36  tff(c_125, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.36  tff(c_129, plain, (![A_12, B_68]: (k9_subset_1(A_12, B_68, '#skF_4')=k3_xboole_0(B_68, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_125])).
% 2.74/1.36  tff(c_132, plain, (![A_12, B_68]: (k9_subset_1(A_12, B_68, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_129])).
% 2.74/1.36  tff(c_140, plain, (![A_72, C_73, B_74]: (k9_subset_1(A_72, C_73, B_74)=k9_subset_1(A_72, B_74, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.36  tff(c_144, plain, (![A_12, B_74]: (k9_subset_1(A_12, B_74, '#skF_4')=k9_subset_1(A_12, '#skF_4', B_74))), inference(resolution, [status(thm)], [c_80, c_140])).
% 2.74/1.36  tff(c_147, plain, (![A_12, B_74]: (k9_subset_1(A_12, '#skF_4', B_74)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_144])).
% 2.74/1.36  tff(c_621, plain, (![A_123, B_124, D_125]: (k9_subset_1(u1_struct_0(A_123), B_124, D_125)!='#skF_2'(A_123, B_124) | ~v4_pre_topc(D_125, A_123) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.74/1.36  tff(c_634, plain, (![A_123, B_74]: ('#skF_2'(A_123, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_74, A_123) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2('#skF_4', A_123) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_147, c_621])).
% 2.74/1.36  tff(c_650, plain, (![A_126, B_127]: ('#skF_2'(A_126, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | v2_tex_2('#skF_4', A_126) | ~l1_pre_topc(A_126))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_634])).
% 2.74/1.36  tff(c_659, plain, (![B_127]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v4_pre_topc(B_127, '#skF_3') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_650])).
% 2.74/1.36  tff(c_671, plain, (![B_127]: (~v4_pre_topc(B_127, '#skF_3') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_270, c_659])).
% 2.74/1.36  tff(c_675, plain, (![B_128]: (~v4_pre_topc(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_671])).
% 2.74/1.36  tff(c_688, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_51, c_675])).
% 2.74/1.36  tff(c_692, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_688])).
% 2.74/1.36  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_692])).
% 2.74/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.36  
% 2.74/1.36  Inference rules
% 2.74/1.36  ----------------------
% 2.74/1.36  #Ref     : 0
% 2.74/1.36  #Sup     : 141
% 2.74/1.36  #Fact    : 0
% 2.74/1.36  #Define  : 0
% 2.74/1.36  #Split   : 3
% 2.74/1.36  #Chain   : 0
% 2.74/1.36  #Close   : 0
% 2.74/1.36  
% 2.74/1.36  Ordering : KBO
% 2.74/1.36  
% 2.74/1.36  Simplification rules
% 2.74/1.36  ----------------------
% 2.74/1.36  #Subsume      : 9
% 2.74/1.36  #Demod        : 123
% 2.74/1.36  #Tautology    : 65
% 2.74/1.36  #SimpNegUnit  : 12
% 2.74/1.36  #BackRed      : 1
% 2.74/1.36  
% 2.74/1.36  #Partial instantiations: 0
% 2.74/1.36  #Strategies tried      : 1
% 2.74/1.36  
% 2.74/1.36  Timing (in seconds)
% 2.74/1.36  ----------------------
% 2.74/1.36  Preprocessing        : 0.31
% 2.74/1.36  Parsing              : 0.17
% 2.74/1.36  CNF conversion       : 0.02
% 2.74/1.36  Main loop            : 0.32
% 2.94/1.36  Inferencing          : 0.12
% 2.94/1.36  Reduction            : 0.10
% 2.94/1.36  Demodulation         : 0.07
% 2.94/1.36  BG Simplification    : 0.02
% 2.94/1.36  Subsumption          : 0.05
% 2.94/1.36  Abstraction          : 0.02
% 2.94/1.36  MUC search           : 0.00
% 2.94/1.36  Cooper               : 0.00
% 2.94/1.36  Total                : 0.67
% 2.94/1.36  Index Insertion      : 0.00
% 2.94/1.36  Index Deletion       : 0.00
% 2.94/1.36  Index Matching       : 0.00
% 2.94/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
