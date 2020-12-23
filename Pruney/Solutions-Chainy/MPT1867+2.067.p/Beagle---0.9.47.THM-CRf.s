%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   68 (  88 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  175 ( 264 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_pre_topc(B,A)
          & ~ v2_struct_0(B)
          & v7_struct_0(B)
          & v1_pre_topc(B)
          & v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc10_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v1_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tex_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_112,axiom,(
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

tff(f_126,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_94,plain,(
    ! [A_55] :
      ( m1_pre_topc('#skF_1'(A_55),A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( l1_pre_topc(B_10)
      | ~ m1_pre_topc(B_10,A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,(
    ! [A_55] :
      ( l1_pre_topc('#skF_1'(A_55))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_94,c_12])).

tff(c_22,plain,(
    ! [A_15] :
      ( v2_pre_topc('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_15] :
      ( v7_struct_0('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100,plain,(
    ! [A_57] :
      ( ~ v7_struct_0(A_57)
      | v1_tdlat_3(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,(
    ! [A_65] :
      ( v1_tdlat_3('#skF_1'(A_65))
      | ~ v2_pre_topc('#skF_1'(A_65))
      | v2_struct_0('#skF_1'(A_65))
      | ~ l1_pre_topc('#skF_1'(A_65))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_28,plain,(
    ! [A_15] :
      ( ~ v2_struct_0('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_155,plain,(
    ! [A_75] :
      ( v1_tdlat_3('#skF_1'(A_75))
      | ~ v2_pre_topc('#skF_1'(A_75))
      | ~ l1_pre_topc('#skF_1'(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_115,c_28])).

tff(c_159,plain,(
    ! [A_15] :
      ( v1_tdlat_3('#skF_1'(A_15))
      | ~ l1_pre_topc('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_30,plain,(
    ! [A_15] :
      ( m1_pre_topc('#skF_1'(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_171,plain,(
    ! [B_81,A_82] :
      ( v2_tex_2(u1_struct_0(B_81),A_82)
      | ~ v1_tdlat_3(B_81)
      | ~ m1_subset_1(u1_struct_0(B_81),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_pre_topc(B_81,A_82)
      | v2_struct_0(B_81)
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_180,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(u1_struct_0(B_83),A_84)
      | ~ v1_tdlat_3(B_83)
      | v2_struct_0(B_83)
      | v2_struct_0(A_84)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_42,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_50])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_71,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(resolution,[status(thm)],[c_56,c_71])).

tff(c_120,plain,(
    ! [C_66,A_67,B_68] :
      ( v2_tex_2(C_66,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ r1_tarski(C_66,B_68)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_124,plain,(
    ! [A_67,A_2] :
      ( v2_tex_2('#skF_3',A_67)
      | ~ v2_tex_2(A_2,A_67)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_79,c_120])).

tff(c_129,plain,(
    ! [A_69,A_70] :
      ( v2_tex_2('#skF_3',A_69)
      | ~ v2_tex_2(A_70,A_69)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_124])).

tff(c_141,plain,(
    ! [A_11,B_13] :
      ( v2_tex_2('#skF_3',A_11)
      | ~ v2_tex_2(u1_struct_0(B_13),A_11)
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_129])).

tff(c_189,plain,(
    ! [A_85,B_86] :
      ( v2_tex_2('#skF_3',A_85)
      | ~ v1_tdlat_3(B_86)
      | v2_struct_0(B_86)
      | v2_struct_0(A_85)
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_180,c_141])).

tff(c_193,plain,(
    ! [A_87] :
      ( v2_tex_2('#skF_3',A_87)
      | ~ v1_tdlat_3('#skF_1'(A_87))
      | v2_struct_0('#skF_1'(A_87))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_30,c_189])).

tff(c_198,plain,(
    ! [A_88] :
      ( v2_tex_2('#skF_3',A_88)
      | ~ v1_tdlat_3('#skF_1'(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_193,c_28])).

tff(c_203,plain,(
    ! [A_89] :
      ( v2_tex_2('#skF_3',A_89)
      | ~ l1_pre_topc('#skF_1'(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_159,c_198])).

tff(c_208,plain,(
    ! [A_90] :
      ( v2_tex_2('#skF_3',A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_98,c_203])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_211,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_208,c_38])).

tff(c_214,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.25  
% 2.29/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.26  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.29/1.26  
% 2.29/1.26  %Foreground sorts:
% 2.29/1.26  
% 2.29/1.26  
% 2.29/1.26  %Background operators:
% 2.29/1.26  
% 2.29/1.26  
% 2.29/1.26  %Foreground operators:
% 2.29/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.26  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.29/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.26  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.29/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.29/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.26  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.29/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.29/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.26  
% 2.45/1.27  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.45/1.27  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((((m1_pre_topc(B, A) & ~v2_struct_0(B)) & v7_struct_0(B)) & v1_pre_topc(B)) & v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc10_tex_2)).
% 2.45/1.27  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.45/1.27  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v2_pre_topc(A)) & ~v1_tdlat_3(A)) => ((~v2_struct_0(A) & ~v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_tex_1)).
% 2.45/1.27  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.45/1.27  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.45/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.45/1.27  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.45/1.27  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.45/1.27  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.45/1.27  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.45/1.27  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.45/1.27  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.45/1.27  tff(c_94, plain, (![A_55]: (m1_pre_topc('#skF_1'(A_55), A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.27  tff(c_12, plain, (![B_10, A_8]: (l1_pre_topc(B_10) | ~m1_pre_topc(B_10, A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.27  tff(c_98, plain, (![A_55]: (l1_pre_topc('#skF_1'(A_55)) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_94, c_12])).
% 2.45/1.27  tff(c_22, plain, (![A_15]: (v2_pre_topc('#skF_1'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.27  tff(c_26, plain, (![A_15]: (v7_struct_0('#skF_1'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.27  tff(c_100, plain, (![A_57]: (~v7_struct_0(A_57) | v1_tdlat_3(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.45/1.27  tff(c_115, plain, (![A_65]: (v1_tdlat_3('#skF_1'(A_65)) | ~v2_pre_topc('#skF_1'(A_65)) | v2_struct_0('#skF_1'(A_65)) | ~l1_pre_topc('#skF_1'(A_65)) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_26, c_100])).
% 2.45/1.27  tff(c_28, plain, (![A_15]: (~v2_struct_0('#skF_1'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.27  tff(c_155, plain, (![A_75]: (v1_tdlat_3('#skF_1'(A_75)) | ~v2_pre_topc('#skF_1'(A_75)) | ~l1_pre_topc('#skF_1'(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_115, c_28])).
% 2.45/1.27  tff(c_159, plain, (![A_15]: (v1_tdlat_3('#skF_1'(A_15)) | ~l1_pre_topc('#skF_1'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(resolution, [status(thm)], [c_22, c_155])).
% 2.45/1.27  tff(c_30, plain, (![A_15]: (m1_pre_topc('#skF_1'(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.45/1.27  tff(c_14, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.27  tff(c_171, plain, (![B_81, A_82]: (v2_tex_2(u1_struct_0(B_81), A_82) | ~v1_tdlat_3(B_81) | ~m1_subset_1(u1_struct_0(B_81), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_pre_topc(B_81, A_82) | v2_struct_0(B_81) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.45/1.27  tff(c_180, plain, (![B_83, A_84]: (v2_tex_2(u1_struct_0(B_83), A_84) | ~v1_tdlat_3(B_83) | v2_struct_0(B_83) | v2_struct_0(A_84) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_14, c_171])).
% 2.45/1.27  tff(c_42, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.45/1.27  tff(c_50, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.27  tff(c_54, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_50])).
% 2.45/1.27  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.27  tff(c_56, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4])).
% 2.45/1.27  tff(c_71, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.27  tff(c_79, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(resolution, [status(thm)], [c_56, c_71])).
% 2.45/1.27  tff(c_120, plain, (![C_66, A_67, B_68]: (v2_tex_2(C_66, A_67) | ~v2_tex_2(B_68, A_67) | ~r1_tarski(C_66, B_68) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.45/1.27  tff(c_124, plain, (![A_67, A_2]: (v2_tex_2('#skF_3', A_67) | ~v2_tex_2(A_2, A_67) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_79, c_120])).
% 2.45/1.27  tff(c_129, plain, (![A_69, A_70]: (v2_tex_2('#skF_3', A_69) | ~v2_tex_2(A_70, A_69) | ~m1_subset_1(A_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_124])).
% 2.45/1.27  tff(c_141, plain, (![A_11, B_13]: (v2_tex_2('#skF_3', A_11) | ~v2_tex_2(u1_struct_0(B_13), A_11) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_14, c_129])).
% 2.45/1.27  tff(c_189, plain, (![A_85, B_86]: (v2_tex_2('#skF_3', A_85) | ~v1_tdlat_3(B_86) | v2_struct_0(B_86) | v2_struct_0(A_85) | ~m1_pre_topc(B_86, A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_180, c_141])).
% 2.45/1.27  tff(c_193, plain, (![A_87]: (v2_tex_2('#skF_3', A_87) | ~v1_tdlat_3('#skF_1'(A_87)) | v2_struct_0('#skF_1'(A_87)) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_30, c_189])).
% 2.45/1.27  tff(c_198, plain, (![A_88]: (v2_tex_2('#skF_3', A_88) | ~v1_tdlat_3('#skF_1'(A_88)) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_193, c_28])).
% 2.45/1.27  tff(c_203, plain, (![A_89]: (v2_tex_2('#skF_3', A_89) | ~l1_pre_topc('#skF_1'(A_89)) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_159, c_198])).
% 2.45/1.27  tff(c_208, plain, (![A_90]: (v2_tex_2('#skF_3', A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_98, c_203])).
% 2.45/1.27  tff(c_38, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.45/1.27  tff(c_211, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_208, c_38])).
% 2.45/1.27  tff(c_214, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_211])).
% 2.45/1.27  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_214])).
% 2.45/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.27  
% 2.45/1.27  Inference rules
% 2.45/1.27  ----------------------
% 2.45/1.27  #Ref     : 0
% 2.45/1.27  #Sup     : 32
% 2.45/1.27  #Fact    : 0
% 2.45/1.27  #Define  : 0
% 2.45/1.27  #Split   : 0
% 2.45/1.27  #Chain   : 0
% 2.45/1.27  #Close   : 0
% 2.45/1.27  
% 2.45/1.27  Ordering : KBO
% 2.45/1.27  
% 2.45/1.27  Simplification rules
% 2.45/1.27  ----------------------
% 2.45/1.27  #Subsume      : 9
% 2.45/1.27  #Demod        : 6
% 2.45/1.27  #Tautology    : 10
% 2.45/1.27  #SimpNegUnit  : 1
% 2.45/1.27  #BackRed      : 2
% 2.45/1.27  
% 2.45/1.27  #Partial instantiations: 0
% 2.45/1.27  #Strategies tried      : 1
% 2.45/1.27  
% 2.45/1.27  Timing (in seconds)
% 2.45/1.27  ----------------------
% 2.45/1.28  Preprocessing        : 0.30
% 2.45/1.28  Parsing              : 0.17
% 2.45/1.28  CNF conversion       : 0.02
% 2.45/1.28  Main loop            : 0.22
% 2.45/1.28  Inferencing          : 0.10
% 2.45/1.28  Reduction            : 0.05
% 2.45/1.28  Demodulation         : 0.04
% 2.45/1.28  BG Simplification    : 0.01
% 2.45/1.28  Subsumption          : 0.04
% 2.45/1.28  Abstraction          : 0.01
% 2.45/1.28  MUC search           : 0.00
% 2.45/1.28  Cooper               : 0.00
% 2.45/1.28  Total                : 0.56
% 2.45/1.28  Index Insertion      : 0.00
% 2.45/1.28  Index Deletion       : 0.00
% 2.45/1.28  Index Matching       : 0.00
% 2.45/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
