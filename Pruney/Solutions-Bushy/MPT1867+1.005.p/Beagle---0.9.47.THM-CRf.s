%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1867+1.005 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 335 expanded)
%              Number of leaves         :   30 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 733 expanded)
%              Number of equality atoms :   22 ( 131 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_63,axiom,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_22,plain,(
    ! [A_38] : v1_xboole_0('#skF_3'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [A_38] : '#skF_3'(A_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_62,plain,(
    ! [A_38] : '#skF_3'(A_38) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55])).

tff(c_24,plain,(
    ! [A_38] : m1_subset_1('#skF_3'(A_38),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ! [A_38] : m1_subset_1('#skF_5',k1_zfmisc_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_221,plain,(
    ! [A_85,B_86] :
      ( r1_tarski('#skF_2'(A_85,B_86),B_86)
      | v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_366,plain,(
    ! [A_102] :
      ( r1_tarski('#skF_2'(A_102,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_78,c_221])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_95,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(A_43)
      | ~ v1_xboole_0(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_30,c_95])).

tff(c_371,plain,(
    ! [A_102] :
      ( v1_xboole_0('#skF_2'(A_102,'#skF_5'))
      | ~ v1_xboole_0('#skF_5')
      | v2_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_366,c_102])).

tff(c_376,plain,(
    ! [A_103] :
      ( v1_xboole_0('#skF_2'(A_103,'#skF_5'))
      | v2_tex_2('#skF_5',A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_371])).

tff(c_32,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    ! [A_45] :
      ( A_45 = '#skF_5'
      | ~ v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_384,plain,(
    ! [A_104] :
      ( '#skF_2'(A_104,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_376,c_57])).

tff(c_387,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_384,c_36])).

tff(c_390,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_387])).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_291,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1('#skF_2'(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v3_pre_topc(B_6,A_4)
      | ~ v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1151,plain,(
    ! [A_190,B_191] :
      ( v3_pre_topc('#skF_2'(A_190,B_191),A_190)
      | ~ v1_xboole_0('#skF_2'(A_190,B_191))
      | ~ v2_pre_topc(A_190)
      | v2_tex_2(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(resolution,[status(thm)],[c_291,c_4])).

tff(c_1170,plain,(
    ! [A_192] :
      ( v3_pre_topc('#skF_2'(A_192,'#skF_5'),A_192)
      | ~ v1_xboole_0('#skF_2'(A_192,'#skF_5'))
      | ~ v2_pre_topc(A_192)
      | v2_tex_2('#skF_5',A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_78,c_1151])).

tff(c_1173,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_1170])).

tff(c_1175,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_40,c_390,c_1173])).

tff(c_1176,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1175])).

tff(c_153,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,C_78) = k3_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_163,plain,(
    ! [A_79,B_80] : k9_subset_1(A_79,B_80,'#skF_5') = k3_xboole_0(B_80,'#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_153])).

tff(c_119,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k9_subset_1(A_68,B_69,C_70),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_130,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k9_subset_1(A_68,B_69,C_70),A_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_119,c_28])).

tff(c_169,plain,(
    ! [B_80,A_79] :
      ( r1_tarski(k3_xboole_0(B_80,'#skF_5'),A_79)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_130])).

tff(c_213,plain,(
    ! [B_83,A_84] : r1_tarski(k3_xboole_0(B_83,'#skF_5'),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_169])).

tff(c_219,plain,(
    ! [B_83,A_84] :
      ( v1_xboole_0(k3_xboole_0(B_83,'#skF_5'))
      | ~ v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_213,c_102])).

tff(c_259,plain,(
    ! [A_84] : ~ v1_xboole_0(A_84) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_40])).

tff(c_265,plain,(
    ! [B_89] : v1_xboole_0(k3_xboole_0(B_89,'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_274,plain,(
    ! [B_89] : k3_xboole_0(B_89,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_265,c_57])).

tff(c_162,plain,(
    ! [A_38,B_77] : k9_subset_1(A_38,B_77,'#skF_5') = k3_xboole_0(B_77,'#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_153])).

tff(c_280,plain,(
    ! [A_38,B_77] : k9_subset_1(A_38,B_77,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_162])).

tff(c_391,plain,(
    ! [A_105,B_106,D_107] :
      ( k9_subset_1(u1_struct_0(A_105),B_106,D_107) != '#skF_2'(A_105,B_106)
      | ~ v3_pre_topc(D_107,A_105)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_394,plain,(
    ! [A_105,B_77] :
      ( '#skF_2'(A_105,B_77) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_105)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_77,A_105)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_391])).

tff(c_2161,plain,(
    ! [A_267,B_268] :
      ( '#skF_2'(A_267,B_268) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_267)
      | v2_tex_2(B_268,A_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_394])).

tff(c_2185,plain,(
    ! [A_269] :
      ( '#skF_2'(A_269,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_269)
      | v2_tex_2('#skF_5',A_269)
      | ~ l1_pre_topc(A_269) ) ),
    inference(resolution,[status(thm)],[c_78,c_2161])).

tff(c_2188,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1176,c_2185])).

tff(c_2194,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_390,c_2188])).

tff(c_2196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2194])).

%------------------------------------------------------------------------------
