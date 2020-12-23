%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:25 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 178 expanded)
%              Number of leaves         :   32 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  125 ( 362 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_14,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [A_13] : m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_182,plain,(
    ! [A_82,B_83] :
      ( r1_tarski('#skF_3'(A_82,B_83),B_83)
      | v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_193,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_3'(A_85,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_52,c_182])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ r1_tarski(A_6,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_8])).

tff(c_198,plain,(
    ! [A_86] :
      ( '#skF_3'(A_86,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_193,c_65])).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_201,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_34])).

tff(c_204,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201])).

tff(c_134,plain,(
    ! [B_76,A_77] :
      ( v3_pre_topc(B_76,A_77)
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_146,plain,(
    ! [A_77] :
      ( v3_pre_topc('#skF_5',A_77)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_52,c_134])).

tff(c_151,plain,(
    ! [A_77] :
      ( v3_pre_topc('#skF_5',A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_146])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [A_13,B_65] : k9_subset_1(A_13,B_65,'#skF_5') = k3_xboole_0(B_65,'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_102,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1(k9_subset_1(A_69,B_70,C_71),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [B_65,A_13] :
      ( m1_subset_1(k3_xboole_0(B_65,'#skF_5'),k1_zfmisc_1(A_13))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_102])).

tff(c_117,plain,(
    ! [B_72,A_73] : m1_subset_1(k3_xboole_0(B_72,'#skF_5'),k1_zfmisc_1(A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_111])).

tff(c_18,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_126,plain,(
    ! [A_73,A_17,B_72] :
      ( ~ v1_xboole_0(A_73)
      | ~ r2_hidden(A_17,k3_xboole_0(B_72,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_128,plain,(
    ! [A_74,B_75] : ~ r2_hidden(A_74,k3_xboole_0(B_75,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_152,plain,(
    ! [B_78] : v1_xboole_0(k3_xboole_0(B_78,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_156,plain,(
    ! [B_78] : k3_xboole_0(B_78,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_152,c_51])).

tff(c_160,plain,(
    ! [A_13,B_65] : k9_subset_1(A_13,B_65,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_92])).

tff(c_312,plain,(
    ! [A_111,B_112,D_113] :
      ( k9_subset_1(u1_struct_0(A_111),B_112,D_113) != '#skF_3'(A_111,B_112)
      | ~ v3_pre_topc(D_113,A_111)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(u1_struct_0(A_111)))
      | v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_315,plain,(
    ! [A_111,B_65] :
      ( '#skF_3'(A_111,B_65) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_111)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_111)))
      | v2_tex_2(B_65,A_111)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_312])).

tff(c_455,plain,(
    ! [A_129,B_130] :
      ( '#skF_3'(A_129,B_130) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_129)
      | v2_tex_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_315])).

tff(c_479,plain,(
    ! [A_131] :
      ( '#skF_3'(A_131,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_131)
      | v2_tex_2('#skF_5',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_52,c_455])).

tff(c_484,plain,(
    ! [A_132] :
      ( '#skF_3'(A_132,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_151,c_479])).

tff(c_487,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_484,c_34])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_204,c_487])).

tff(c_492,plain,(
    ! [A_73] : ~ v1_xboole_0(A_73) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.38/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.38/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.38/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.38/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.32  
% 2.68/1.34  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.68/1.34  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.68/1.34  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.34  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.68/1.34  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.68/1.34  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.68/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.68/1.34  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.68/1.34  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.68/1.34  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.34  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.34  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.34  tff(c_38, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.34  tff(c_46, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.34  tff(c_50, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.68/1.34  tff(c_14, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.34  tff(c_52, plain, (![A_13]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 2.68/1.34  tff(c_182, plain, (![A_82, B_83]: (r1_tarski('#skF_3'(A_82, B_83), B_83) | v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.34  tff(c_193, plain, (![A_85]: (r1_tarski('#skF_3'(A_85, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_52, c_182])).
% 2.68/1.34  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.34  tff(c_65, plain, (![A_6]: (A_6='#skF_5' | ~r1_tarski(A_6, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_8])).
% 2.68/1.34  tff(c_198, plain, (![A_86]: ('#skF_3'(A_86, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_193, c_65])).
% 2.68/1.34  tff(c_34, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.68/1.34  tff(c_201, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_198, c_34])).
% 2.68/1.34  tff(c_204, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201])).
% 2.68/1.34  tff(c_134, plain, (![B_76, A_77]: (v3_pre_topc(B_76, A_77) | ~v1_xboole_0(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.34  tff(c_146, plain, (![A_77]: (v3_pre_topc('#skF_5', A_77) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(resolution, [status(thm)], [c_52, c_134])).
% 2.68/1.34  tff(c_151, plain, (![A_77]: (v3_pre_topc('#skF_5', A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_146])).
% 2.68/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.34  tff(c_89, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.34  tff(c_92, plain, (![A_13, B_65]: (k9_subset_1(A_13, B_65, '#skF_5')=k3_xboole_0(B_65, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 2.68/1.34  tff(c_102, plain, (![A_69, B_70, C_71]: (m1_subset_1(k9_subset_1(A_69, B_70, C_71), k1_zfmisc_1(A_69)) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.34  tff(c_111, plain, (![B_65, A_13]: (m1_subset_1(k3_xboole_0(B_65, '#skF_5'), k1_zfmisc_1(A_13)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_102])).
% 2.68/1.34  tff(c_117, plain, (![B_72, A_73]: (m1_subset_1(k3_xboole_0(B_72, '#skF_5'), k1_zfmisc_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_111])).
% 2.68/1.34  tff(c_18, plain, (![C_19, B_18, A_17]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.68/1.34  tff(c_126, plain, (![A_73, A_17, B_72]: (~v1_xboole_0(A_73) | ~r2_hidden(A_17, k3_xboole_0(B_72, '#skF_5')))), inference(resolution, [status(thm)], [c_117, c_18])).
% 2.68/1.34  tff(c_128, plain, (![A_74, B_75]: (~r2_hidden(A_74, k3_xboole_0(B_75, '#skF_5')))), inference(splitLeft, [status(thm)], [c_126])).
% 2.68/1.34  tff(c_152, plain, (![B_78]: (v1_xboole_0(k3_xboole_0(B_78, '#skF_5')))), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.68/1.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.34  tff(c_51, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 2.68/1.34  tff(c_156, plain, (![B_78]: (k3_xboole_0(B_78, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_152, c_51])).
% 2.68/1.34  tff(c_160, plain, (![A_13, B_65]: (k9_subset_1(A_13, B_65, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_92])).
% 2.68/1.34  tff(c_312, plain, (![A_111, B_112, D_113]: (k9_subset_1(u1_struct_0(A_111), B_112, D_113)!='#skF_3'(A_111, B_112) | ~v3_pre_topc(D_113, A_111) | ~m1_subset_1(D_113, k1_zfmisc_1(u1_struct_0(A_111))) | v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.34  tff(c_315, plain, (![A_111, B_65]: ('#skF_3'(A_111, B_65)!='#skF_5' | ~v3_pre_topc('#skF_5', A_111) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_111))) | v2_tex_2(B_65, A_111) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(superposition, [status(thm), theory('equality')], [c_160, c_312])).
% 2.68/1.34  tff(c_455, plain, (![A_129, B_130]: ('#skF_3'(A_129, B_130)!='#skF_5' | ~v3_pre_topc('#skF_5', A_129) | v2_tex_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_315])).
% 2.68/1.34  tff(c_479, plain, (![A_131]: ('#skF_3'(A_131, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_131) | v2_tex_2('#skF_5', A_131) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_52, c_455])).
% 2.68/1.34  tff(c_484, plain, (![A_132]: ('#skF_3'(A_132, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(resolution, [status(thm)], [c_151, c_479])).
% 2.68/1.34  tff(c_487, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_484, c_34])).
% 2.68/1.34  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_204, c_487])).
% 2.68/1.34  tff(c_492, plain, (![A_73]: (~v1_xboole_0(A_73))), inference(splitRight, [status(thm)], [c_126])).
% 2.68/1.34  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_38])).
% 2.68/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  Inference rules
% 2.68/1.34  ----------------------
% 2.68/1.34  #Ref     : 0
% 2.68/1.34  #Sup     : 101
% 2.68/1.34  #Fact    : 0
% 2.68/1.34  #Define  : 0
% 2.68/1.34  #Split   : 2
% 2.68/1.34  #Chain   : 0
% 2.68/1.34  #Close   : 0
% 2.68/1.34  
% 2.68/1.34  Ordering : KBO
% 2.68/1.34  
% 2.68/1.34  Simplification rules
% 2.68/1.34  ----------------------
% 2.68/1.34  #Subsume      : 13
% 2.68/1.34  #Demod        : 62
% 2.68/1.34  #Tautology    : 35
% 2.68/1.34  #SimpNegUnit  : 4
% 2.68/1.34  #BackRed      : 8
% 2.68/1.34  
% 2.68/1.34  #Partial instantiations: 0
% 2.68/1.34  #Strategies tried      : 1
% 2.68/1.34  
% 2.68/1.34  Timing (in seconds)
% 2.68/1.34  ----------------------
% 2.68/1.34  Preprocessing        : 0.31
% 2.68/1.34  Parsing              : 0.17
% 2.68/1.34  CNF conversion       : 0.02
% 2.68/1.34  Main loop            : 0.28
% 2.68/1.34  Inferencing          : 0.10
% 2.68/1.34  Reduction            : 0.08
% 2.68/1.34  Demodulation         : 0.06
% 2.68/1.34  BG Simplification    : 0.02
% 2.68/1.34  Subsumption          : 0.06
% 2.68/1.34  Abstraction          : 0.02
% 2.68/1.34  MUC search           : 0.00
% 2.68/1.34  Cooper               : 0.00
% 2.68/1.34  Total                : 0.62
% 2.68/1.34  Index Insertion      : 0.00
% 2.68/1.34  Index Deletion       : 0.00
% 2.68/1.34  Index Matching       : 0.00
% 2.68/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
