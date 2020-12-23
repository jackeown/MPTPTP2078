%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 170 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  121 ( 341 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_107,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_12,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_183,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_3'(A_80,B_81),B_81)
      | v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_216,plain,(
    ! [A_84] :
      ( r1_tarski('#skF_3'(A_84,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_54,c_183])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_2] :
      ( A_2 = '#skF_5'
      | ~ r1_tarski(A_2,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_4])).

tff(c_221,plain,(
    ! [A_85] :
      ( '#skF_3'(A_85,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_216,c_67])).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_224,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_36])).

tff(c_227,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_224])).

tff(c_18,plain,(
    ! [A_19] :
      ( v4_pre_topc('#skF_1'(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'(A_19),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_12,B_64] : k9_subset_1(A_12,B_64,'#skF_5') = k3_xboole_0(B_64,'#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_107,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k9_subset_1(A_68,B_69,C_70),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [B_64,A_12] :
      ( m1_subset_1(k3_xboole_0(B_64,'#skF_5'),k1_zfmisc_1(A_12))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_107])).

tff(c_123,plain,(
    ! [B_71,A_72] : m1_subset_1(k3_xboole_0(B_71,'#skF_5'),k1_zfmisc_1(A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_117])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_133,plain,(
    ! [B_71,A_72] :
      ( v1_xboole_0(k3_xboole_0(B_71,'#skF_5'))
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_123,c_14])).

tff(c_134,plain,(
    ! [A_72] : ~ v1_xboole_0(A_72) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_40])).

tff(c_154,plain,(
    ! [B_76] : v1_xboole_0(k3_xboole_0(B_76,'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_158,plain,(
    ! [B_76] : k3_xboole_0(B_76,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_154,c_53])).

tff(c_140,plain,(
    ! [A_73,C_74,B_75] :
      ( k9_subset_1(A_73,C_74,B_75) = k9_subset_1(A_73,B_75,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [A_12,B_75] : k9_subset_1(A_12,B_75,'#skF_5') = k9_subset_1(A_12,'#skF_5',B_75) ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_153,plain,(
    ! [A_12,B_75] : k9_subset_1(A_12,'#skF_5',B_75) = k3_xboole_0(B_75,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_148])).

tff(c_195,plain,(
    ! [A_12,B_75] : k9_subset_1(A_12,'#skF_5',B_75) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_153])).

tff(c_339,plain,(
    ! [A_103,B_104,D_105] :
      ( k9_subset_1(u1_struct_0(A_103),B_104,D_105) != '#skF_3'(A_103,B_104)
      | ~ v4_pre_topc(D_105,A_103)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | v2_tex_2(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_344,plain,(
    ! [A_103,B_75] :
      ( '#skF_3'(A_103,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_75,A_103)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_103)))
      | v2_tex_2('#skF_5',A_103)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_339])).

tff(c_702,plain,(
    ! [A_149,B_150] :
      ( '#skF_3'(A_149,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc(B_150,A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | v2_tex_2('#skF_5',A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_344])).

tff(c_726,plain,(
    ! [A_152] :
      ( '#skF_3'(A_152,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_1'(A_152),A_152)
      | v2_tex_2('#skF_5',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_22,c_702])).

tff(c_731,plain,(
    ! [A_153] :
      ( '#skF_3'(A_153,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_18,c_726])).

tff(c_734,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_731,c_36])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_227,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.40  
% 3.03/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.40  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.03/1.40  
% 3.03/1.40  %Foreground sorts:
% 3.03/1.40  
% 3.03/1.40  
% 3.03/1.40  %Background operators:
% 3.03/1.40  
% 3.03/1.40  
% 3.03/1.40  %Foreground operators:
% 3.03/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.03/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.03/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.03/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.03/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.40  tff('#skF_5', type, '#skF_5': $i).
% 3.03/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.03/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.03/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.03/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.40  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.03/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.03/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.40  
% 3.03/1.42  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.03/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.03/1.42  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.03/1.42  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.03/1.42  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.03/1.42  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_tops_1)).
% 3.03/1.42  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.03/1.42  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.03/1.42  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.03/1.42  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.03/1.42  tff(c_44, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.03/1.42  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.03/1.42  tff(c_40, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.03/1.42  tff(c_48, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.42  tff(c_52, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_48])).
% 3.03/1.42  tff(c_12, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.03/1.42  tff(c_54, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 3.03/1.42  tff(c_183, plain, (![A_80, B_81]: (r1_tarski('#skF_3'(A_80, B_81), B_81) | v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.42  tff(c_216, plain, (![A_84]: (r1_tarski('#skF_3'(A_84, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_54, c_183])).
% 3.03/1.42  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.42  tff(c_67, plain, (![A_2]: (A_2='#skF_5' | ~r1_tarski(A_2, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_4])).
% 3.03/1.42  tff(c_221, plain, (![A_85]: ('#skF_3'(A_85, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_216, c_67])).
% 3.03/1.42  tff(c_36, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.03/1.42  tff(c_224, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_221, c_36])).
% 3.03/1.42  tff(c_227, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_224])).
% 3.03/1.42  tff(c_18, plain, (![A_19]: (v4_pre_topc('#skF_1'(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.42  tff(c_22, plain, (![A_19]: (m1_subset_1('#skF_1'(A_19), k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.42  tff(c_91, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.42  tff(c_97, plain, (![A_12, B_64]: (k9_subset_1(A_12, B_64, '#skF_5')=k3_xboole_0(B_64, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_91])).
% 3.03/1.42  tff(c_107, plain, (![A_68, B_69, C_70]: (m1_subset_1(k9_subset_1(A_68, B_69, C_70), k1_zfmisc_1(A_68)) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.03/1.42  tff(c_117, plain, (![B_64, A_12]: (m1_subset_1(k3_xboole_0(B_64, '#skF_5'), k1_zfmisc_1(A_12)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_107])).
% 3.03/1.42  tff(c_123, plain, (![B_71, A_72]: (m1_subset_1(k3_xboole_0(B_71, '#skF_5'), k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_117])).
% 3.03/1.42  tff(c_14, plain, (![B_15, A_13]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.42  tff(c_133, plain, (![B_71, A_72]: (v1_xboole_0(k3_xboole_0(B_71, '#skF_5')) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_123, c_14])).
% 3.03/1.42  tff(c_134, plain, (![A_72]: (~v1_xboole_0(A_72))), inference(splitLeft, [status(thm)], [c_133])).
% 3.03/1.42  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_40])).
% 3.03/1.42  tff(c_154, plain, (![B_76]: (v1_xboole_0(k3_xboole_0(B_76, '#skF_5')))), inference(splitRight, [status(thm)], [c_133])).
% 3.03/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.42  tff(c_53, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 3.03/1.42  tff(c_158, plain, (![B_76]: (k3_xboole_0(B_76, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_154, c_53])).
% 3.03/1.42  tff(c_140, plain, (![A_73, C_74, B_75]: (k9_subset_1(A_73, C_74, B_75)=k9_subset_1(A_73, B_75, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.42  tff(c_148, plain, (![A_12, B_75]: (k9_subset_1(A_12, B_75, '#skF_5')=k9_subset_1(A_12, '#skF_5', B_75))), inference(resolution, [status(thm)], [c_54, c_140])).
% 3.03/1.42  tff(c_153, plain, (![A_12, B_75]: (k9_subset_1(A_12, '#skF_5', B_75)=k3_xboole_0(B_75, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_148])).
% 3.03/1.42  tff(c_195, plain, (![A_12, B_75]: (k9_subset_1(A_12, '#skF_5', B_75)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_153])).
% 3.03/1.42  tff(c_339, plain, (![A_103, B_104, D_105]: (k9_subset_1(u1_struct_0(A_103), B_104, D_105)!='#skF_3'(A_103, B_104) | ~v4_pre_topc(D_105, A_103) | ~m1_subset_1(D_105, k1_zfmisc_1(u1_struct_0(A_103))) | v2_tex_2(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.42  tff(c_344, plain, (![A_103, B_75]: ('#skF_3'(A_103, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_75, A_103) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_103))) | v2_tex_2('#skF_5', A_103) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(superposition, [status(thm), theory('equality')], [c_195, c_339])).
% 3.03/1.42  tff(c_702, plain, (![A_149, B_150]: ('#skF_3'(A_149, '#skF_5')!='#skF_5' | ~v4_pre_topc(B_150, A_149) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | v2_tex_2('#skF_5', A_149) | ~l1_pre_topc(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_344])).
% 3.03/1.42  tff(c_726, plain, (![A_152]: ('#skF_3'(A_152, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_1'(A_152), A_152) | v2_tex_2('#skF_5', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(resolution, [status(thm)], [c_22, c_702])).
% 3.03/1.42  tff(c_731, plain, (![A_153]: ('#skF_3'(A_153, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(resolution, [status(thm)], [c_18, c_726])).
% 3.03/1.42  tff(c_734, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_731, c_36])).
% 3.03/1.42  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_227, c_734])).
% 3.03/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.42  
% 3.03/1.42  Inference rules
% 3.03/1.42  ----------------------
% 3.03/1.42  #Ref     : 0
% 3.03/1.42  #Sup     : 170
% 3.03/1.42  #Fact    : 0
% 3.03/1.42  #Define  : 0
% 3.03/1.42  #Split   : 1
% 3.03/1.42  #Chain   : 0
% 3.03/1.42  #Close   : 0
% 3.03/1.42  
% 3.03/1.42  Ordering : KBO
% 3.03/1.42  
% 3.03/1.42  Simplification rules
% 3.03/1.42  ----------------------
% 3.03/1.42  #Subsume      : 12
% 3.03/1.42  #Demod        : 81
% 3.03/1.42  #Tautology    : 66
% 3.03/1.42  #SimpNegUnit  : 5
% 3.03/1.42  #BackRed      : 6
% 3.03/1.42  
% 3.03/1.42  #Partial instantiations: 0
% 3.03/1.42  #Strategies tried      : 1
% 3.03/1.42  
% 3.03/1.42  Timing (in seconds)
% 3.03/1.42  ----------------------
% 3.03/1.42  Preprocessing        : 0.32
% 3.03/1.42  Parsing              : 0.17
% 3.03/1.42  CNF conversion       : 0.02
% 3.03/1.42  Main loop            : 0.36
% 3.03/1.42  Inferencing          : 0.14
% 3.03/1.42  Reduction            : 0.10
% 3.03/1.42  Demodulation         : 0.07
% 3.03/1.42  BG Simplification    : 0.02
% 3.03/1.42  Subsumption          : 0.07
% 3.03/1.42  Abstraction          : 0.03
% 3.03/1.42  MUC search           : 0.00
% 3.03/1.42  Cooper               : 0.00
% 3.03/1.42  Total                : 0.71
% 3.03/1.42  Index Insertion      : 0.00
% 3.03/1.42  Index Deletion       : 0.00
% 3.03/1.42  Index Matching       : 0.00
% 3.03/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
