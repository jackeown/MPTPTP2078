%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 153 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 313 expanded)
%              Number of equality atoms :   24 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_139,plain,(
    ! [A_69,B_70] :
      ( r1_tarski('#skF_2'(A_69,B_70),B_70)
      | v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_144,plain,(
    ! [A_71] :
      ( r1_tarski('#skF_2'(A_71,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_6])).

tff(c_149,plain,(
    ! [A_72] :
      ( '#skF_2'(A_72,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_144,c_71])).

tff(c_152,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_32])).

tff(c_155,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_152])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tops_1(A_62,B_63),B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [A_66] :
      ( r1_tarski(k1_tops_1(A_66,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_114,plain,(
    ! [A_67] :
      ( k1_tops_1(A_67,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_109,c_71])).

tff(c_118,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_104,plain,(
    ! [A_64,B_65] :
      ( v3_pre_topc(k1_tops_1(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,(
    ! [A_68] :
      ( v3_pre_topc(k1_tops_1(A_68,'#skF_4'),A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_136,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_133])).

tff(c_138,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_136])).

tff(c_4,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_2] : k3_xboole_0(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_4])).

tff(c_86,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_7,B_56] : k9_subset_1(A_7,B_56,'#skF_4') = k3_xboole_0(B_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_90,plain,(
    ! [A_7,B_56] : k9_subset_1(A_7,B_56,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_88])).

tff(c_294,plain,(
    ! [A_98,B_99,D_100] :
      ( k9_subset_1(u1_struct_0(A_98),B_99,D_100) != '#skF_2'(A_98,B_99)
      | ~ v3_pre_topc(D_100,A_98)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(A_98)))
      | v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_299,plain,(
    ! [A_98,B_56] :
      ( '#skF_2'(A_98,B_56) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_98)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_98)))
      | v2_tex_2(B_56,A_98)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_294])).

tff(c_302,plain,(
    ! [A_101,B_102] :
      ( '#skF_2'(A_101,B_102) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_101)
      | v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_299])).

tff(c_316,plain,(
    ! [A_103] :
      ( '#skF_2'(A_103,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_103)
      | v2_tex_2('#skF_4',A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_50,c_302])).

tff(c_319,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_316])).

tff(c_322,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_155,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.38  
% 2.30/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.39  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.30/1.39  
% 2.30/1.39  %Foreground sorts:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Background operators:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Foreground operators:
% 2.30/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.30/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.30/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.30/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.30/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.30/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.39  
% 2.60/1.40  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.60/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.40  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.60/1.40  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.60/1.40  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.60/1.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.60/1.40  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.60/1.40  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.40  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.60/1.40  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.40  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.40  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.40  tff(c_44, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.40  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.60/1.40  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.40  tff(c_50, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 2.60/1.40  tff(c_139, plain, (![A_69, B_70]: (r1_tarski('#skF_2'(A_69, B_70), B_70) | v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.40  tff(c_144, plain, (![A_71]: (r1_tarski('#skF_2'(A_71, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_50, c_139])).
% 2.60/1.40  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.40  tff(c_71, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.60/1.40  tff(c_149, plain, (![A_72]: ('#skF_2'(A_72, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_144, c_71])).
% 2.60/1.40  tff(c_152, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_149, c_32])).
% 2.60/1.40  tff(c_155, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_152])).
% 2.60/1.40  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.40  tff(c_99, plain, (![A_62, B_63]: (r1_tarski(k1_tops_1(A_62, B_63), B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.40  tff(c_109, plain, (![A_66]: (r1_tarski(k1_tops_1(A_66, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_50, c_99])).
% 2.60/1.40  tff(c_114, plain, (![A_67]: (k1_tops_1(A_67, '#skF_4')='#skF_4' | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_109, c_71])).
% 2.60/1.40  tff(c_118, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_114])).
% 2.60/1.40  tff(c_104, plain, (![A_64, B_65]: (v3_pre_topc(k1_tops_1(A_64, B_65), A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.40  tff(c_133, plain, (![A_68]: (v3_pre_topc(k1_tops_1(A_68, '#skF_4'), A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(resolution, [status(thm)], [c_50, c_104])).
% 2.60/1.40  tff(c_136, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_133])).
% 2.60/1.40  tff(c_138, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_136])).
% 2.60/1.40  tff(c_4, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.40  tff(c_55, plain, (![A_2]: (k3_xboole_0(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_4])).
% 2.60/1.40  tff(c_86, plain, (![A_55, B_56, C_57]: (k9_subset_1(A_55, B_56, C_57)=k3_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.40  tff(c_88, plain, (![A_7, B_56]: (k9_subset_1(A_7, B_56, '#skF_4')=k3_xboole_0(B_56, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 2.60/1.40  tff(c_90, plain, (![A_7, B_56]: (k9_subset_1(A_7, B_56, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_88])).
% 2.60/1.40  tff(c_294, plain, (![A_98, B_99, D_100]: (k9_subset_1(u1_struct_0(A_98), B_99, D_100)!='#skF_2'(A_98, B_99) | ~v3_pre_topc(D_100, A_98) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(A_98))) | v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.40  tff(c_299, plain, (![A_98, B_56]: ('#skF_2'(A_98, B_56)!='#skF_4' | ~v3_pre_topc('#skF_4', A_98) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_98))) | v2_tex_2(B_56, A_98) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(superposition, [status(thm), theory('equality')], [c_90, c_294])).
% 2.60/1.40  tff(c_302, plain, (![A_101, B_102]: ('#skF_2'(A_101, B_102)!='#skF_4' | ~v3_pre_topc('#skF_4', A_101) | v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_299])).
% 2.60/1.40  tff(c_316, plain, (![A_103]: ('#skF_2'(A_103, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_103) | v2_tex_2('#skF_4', A_103) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_50, c_302])).
% 2.60/1.40  tff(c_319, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_138, c_316])).
% 2.60/1.40  tff(c_322, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_155, c_319])).
% 2.60/1.40  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_322])).
% 2.60/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  Inference rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Ref     : 0
% 2.60/1.40  #Sup     : 62
% 2.60/1.40  #Fact    : 0
% 2.60/1.40  #Define  : 0
% 2.60/1.40  #Split   : 0
% 2.60/1.40  #Chain   : 0
% 2.60/1.40  #Close   : 0
% 2.60/1.40  
% 2.60/1.40  Ordering : KBO
% 2.60/1.40  
% 2.60/1.40  Simplification rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Subsume      : 1
% 2.60/1.40  #Demod        : 54
% 2.60/1.40  #Tautology    : 25
% 2.60/1.40  #SimpNegUnit  : 10
% 2.60/1.40  #BackRed      : 2
% 2.60/1.40  
% 2.60/1.40  #Partial instantiations: 0
% 2.60/1.40  #Strategies tried      : 1
% 2.60/1.40  
% 2.60/1.40  Timing (in seconds)
% 2.60/1.40  ----------------------
% 2.60/1.41  Preprocessing        : 0.35
% 2.60/1.41  Parsing              : 0.18
% 2.60/1.41  CNF conversion       : 0.03
% 2.60/1.41  Main loop            : 0.24
% 2.60/1.41  Inferencing          : 0.09
% 2.60/1.41  Reduction            : 0.07
% 2.60/1.41  Demodulation         : 0.05
% 2.60/1.41  BG Simplification    : 0.02
% 2.60/1.41  Subsumption          : 0.04
% 2.60/1.41  Abstraction          : 0.02
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.62
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.41  Index Deletion       : 0.00
% 2.60/1.41  Index Matching       : 0.00
% 2.60/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
