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
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 147 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 275 expanded)
%              Number of equality atoms :   37 (  63 expanded)
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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_94,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [A_23] :
      ( v4_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_432,plain,(
    ! [A_96,B_97] :
      ( r1_tarski('#skF_2'(A_96,B_97),B_97)
      | v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_445,plain,(
    ! [A_98] :
      ( r1_tarski('#skF_2'(A_98,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_74,c_432])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_6])).

tff(c_468,plain,(
    ! [A_101] :
      ( '#skF_2'(A_101,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_445,c_84])).

tff(c_471,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_468,c_42])).

tff(c_474,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_471])).

tff(c_26,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_160,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_26,c_140])).

tff(c_164,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_160])).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_169,plain,(
    ! [B_66,A_67] : k1_setfam_1(k2_tarski(B_66,A_67)) = k3_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_145])).

tff(c_20,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_20])).

tff(c_86,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),A_57) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_58] : k3_xboole_0('#skF_4',B_58) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_86,c_84])).

tff(c_208,plain,(
    ! [B_68] : k3_xboole_0(B_68,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_91])).

tff(c_325,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_329,plain,(
    ! [A_15,B_81] : k9_subset_1(A_15,B_81,'#skF_4') = k3_xboole_0(B_81,'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_325])).

tff(c_332,plain,(
    ! [A_15,B_81] : k9_subset_1(A_15,B_81,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_329])).

tff(c_360,plain,(
    ! [A_89,C_90,B_91] :
      ( k9_subset_1(A_89,C_90,B_91) = k9_subset_1(A_89,B_91,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_364,plain,(
    ! [A_15,B_91] : k9_subset_1(A_15,B_91,'#skF_4') = k9_subset_1(A_15,'#skF_4',B_91) ),
    inference(resolution,[status(thm)],[c_74,c_360])).

tff(c_368,plain,(
    ! [A_15,B_91] : k9_subset_1(A_15,'#skF_4',B_91) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_364])).

tff(c_825,plain,(
    ! [A_144,B_145,D_146] :
      ( k9_subset_1(u1_struct_0(A_144),B_145,D_146) != '#skF_2'(A_144,B_145)
      | ~ v4_pre_topc(D_146,A_144)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_835,plain,(
    ! [A_144,B_91] :
      ( '#skF_2'(A_144,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_91,A_144)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_144)))
      | v2_tex_2('#skF_4',A_144)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_825])).

tff(c_854,plain,(
    ! [A_147,B_148] :
      ( '#skF_2'(A_147,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | v2_tex_2('#skF_4',A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_835])).

tff(c_863,plain,(
    ! [B_148] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v4_pre_topc(B_148,'#skF_3')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_854])).

tff(c_875,plain,(
    ! [B_148] :
      ( ~ v4_pre_topc(B_148,'#skF_3')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_474,c_863])).

tff(c_879,plain,(
    ! [B_149] :
      ( ~ v4_pre_topc(B_149,'#skF_3')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_875])).

tff(c_892,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_879])).

tff(c_896,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_892])).

tff(c_900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.87/1.43  
% 2.87/1.43  %Foreground sorts:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Background operators:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Foreground operators:
% 2.87/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.87/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.87/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.87/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.87/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.87/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.87/1.43  
% 2.87/1.44  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.87/1.44  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.87/1.44  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.87/1.44  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.87/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.87/1.44  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.87/1.44  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.87/1.44  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.87/1.44  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.87/1.44  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.87/1.44  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.87/1.44  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.87/1.44  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.87/1.44  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.87/1.44  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.87/1.44  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_28, plain, (![A_23]: (v4_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.44  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.44  tff(c_14, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.44  tff(c_53, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.87/1.44  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.87/1.44  tff(c_64, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.44  tff(c_68, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_64])).
% 2.87/1.44  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.44  tff(c_74, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18])).
% 2.87/1.44  tff(c_432, plain, (![A_96, B_97]: (r1_tarski('#skF_2'(A_96, B_97), B_97) | v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.44  tff(c_445, plain, (![A_98]: (r1_tarski('#skF_2'(A_98, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_74, c_432])).
% 2.87/1.44  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.44  tff(c_84, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_6])).
% 2.87/1.44  tff(c_468, plain, (![A_101]: ('#skF_2'(A_101, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_445, c_84])).
% 2.87/1.44  tff(c_471, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_468, c_42])).
% 2.87/1.44  tff(c_474, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_471])).
% 2.87/1.44  tff(c_26, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.44  tff(c_140, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.44  tff(c_160, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_26, c_140])).
% 2.87/1.44  tff(c_164, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_160])).
% 2.87/1.44  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.44  tff(c_145, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.44  tff(c_169, plain, (![B_66, A_67]: (k1_setfam_1(k2_tarski(B_66, A_67))=k3_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_8, c_145])).
% 2.87/1.44  tff(c_20, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.44  tff(c_192, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_169, c_20])).
% 2.87/1.44  tff(c_86, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.44  tff(c_91, plain, (![B_58]: (k3_xboole_0('#skF_4', B_58)='#skF_4')), inference(resolution, [status(thm)], [c_86, c_84])).
% 2.87/1.44  tff(c_208, plain, (![B_68]: (k3_xboole_0(B_68, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_192, c_91])).
% 2.87/1.44  tff(c_325, plain, (![A_80, B_81, C_82]: (k9_subset_1(A_80, B_81, C_82)=k3_xboole_0(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.44  tff(c_329, plain, (![A_15, B_81]: (k9_subset_1(A_15, B_81, '#skF_4')=k3_xboole_0(B_81, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_325])).
% 2.87/1.44  tff(c_332, plain, (![A_15, B_81]: (k9_subset_1(A_15, B_81, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_329])).
% 2.87/1.44  tff(c_360, plain, (![A_89, C_90, B_91]: (k9_subset_1(A_89, C_90, B_91)=k9_subset_1(A_89, B_91, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.44  tff(c_364, plain, (![A_15, B_91]: (k9_subset_1(A_15, B_91, '#skF_4')=k9_subset_1(A_15, '#skF_4', B_91))), inference(resolution, [status(thm)], [c_74, c_360])).
% 2.87/1.44  tff(c_368, plain, (![A_15, B_91]: (k9_subset_1(A_15, '#skF_4', B_91)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_364])).
% 2.87/1.44  tff(c_825, plain, (![A_144, B_145, D_146]: (k9_subset_1(u1_struct_0(A_144), B_145, D_146)!='#skF_2'(A_144, B_145) | ~v4_pre_topc(D_146, A_144) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_144))) | v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.44  tff(c_835, plain, (![A_144, B_91]: ('#skF_2'(A_144, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_91, A_144) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_144))) | v2_tex_2('#skF_4', A_144) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(superposition, [status(thm), theory('equality')], [c_368, c_825])).
% 2.87/1.44  tff(c_854, plain, (![A_147, B_148]: ('#skF_2'(A_147, '#skF_4')!='#skF_4' | ~v4_pre_topc(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | v2_tex_2('#skF_4', A_147) | ~l1_pre_topc(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_835])).
% 2.87/1.44  tff(c_863, plain, (![B_148]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v4_pre_topc(B_148, '#skF_3') | ~m1_subset_1(B_148, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_854])).
% 2.87/1.44  tff(c_875, plain, (![B_148]: (~v4_pre_topc(B_148, '#skF_3') | ~m1_subset_1(B_148, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_474, c_863])).
% 2.87/1.44  tff(c_879, plain, (![B_149]: (~v4_pre_topc(B_149, '#skF_3') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_875])).
% 2.87/1.44  tff(c_892, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_53, c_879])).
% 2.87/1.44  tff(c_896, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_892])).
% 2.87/1.44  tff(c_900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_896])).
% 2.87/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  Inference rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Ref     : 0
% 2.87/1.44  #Sup     : 188
% 2.87/1.44  #Fact    : 0
% 2.87/1.44  #Define  : 0
% 2.87/1.44  #Split   : 1
% 2.87/1.44  #Chain   : 0
% 2.87/1.44  #Close   : 0
% 2.87/1.44  
% 2.87/1.44  Ordering : KBO
% 2.87/1.44  
% 2.87/1.44  Simplification rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Subsume      : 12
% 2.87/1.44  #Demod        : 143
% 2.87/1.44  #Tautology    : 102
% 2.87/1.44  #SimpNegUnit  : 15
% 2.87/1.44  #BackRed      : 1
% 2.87/1.44  
% 2.87/1.44  #Partial instantiations: 0
% 2.87/1.44  #Strategies tried      : 1
% 2.87/1.44  
% 2.87/1.44  Timing (in seconds)
% 2.87/1.44  ----------------------
% 2.87/1.44  Preprocessing        : 0.32
% 2.87/1.44  Parsing              : 0.17
% 2.87/1.44  CNF conversion       : 0.02
% 2.87/1.44  Main loop            : 0.36
% 2.87/1.44  Inferencing          : 0.13
% 2.87/1.44  Reduction            : 0.12
% 2.87/1.44  Demodulation         : 0.09
% 2.87/1.44  BG Simplification    : 0.02
% 2.87/1.44  Subsumption          : 0.06
% 2.87/1.44  Abstraction          : 0.02
% 2.87/1.44  MUC search           : 0.00
% 2.87/1.44  Cooper               : 0.00
% 2.87/1.44  Total                : 0.71
% 2.87/1.44  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
