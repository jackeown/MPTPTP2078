%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 119 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 251 expanded)
%              Number of equality atoms :   23 (  45 expanded)
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
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_202,plain,(
    ! [A_86,B_87] :
      ( r1_tarski('#skF_2'(A_86,B_87),B_87)
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_219,plain,(
    ! [A_88] :
      ( r1_tarski('#skF_2'(A_88,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_58,c_202])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ r1_tarski(A_5,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_10])).

tff(c_228,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_219,c_75])).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_231,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_34])).

tff(c_234,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_231])).

tff(c_158,plain,(
    ! [B_76,A_77] :
      ( v4_pre_topc(B_76,A_77)
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170,plain,(
    ! [A_77] :
      ( v4_pre_topc('#skF_4',A_77)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_58,c_158])).

tff(c_175,plain,(
    ! [A_77] :
      ( v4_pre_topc('#skF_4',A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_170])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_83,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_4] : k3_xboole_0('#skF_4',A_4) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_59,c_83])).

tff(c_100,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_103,plain,(
    ! [A_12,B_61] : k9_subset_1(A_12,B_61,'#skF_4') = k3_xboole_0(B_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_493,plain,(
    ! [A_130,B_131,D_132] :
      ( k9_subset_1(u1_struct_0(A_130),B_131,D_132) != '#skF_2'(A_130,B_131)
      | ~ v4_pre_topc(D_132,A_130)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_502,plain,(
    ! [B_61,A_130] :
      ( k3_xboole_0(B_61,'#skF_4') != '#skF_2'(A_130,B_61)
      | ~ v4_pre_topc('#skF_4',A_130)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_130)))
      | v2_tex_2(B_61,A_130)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_493])).

tff(c_1054,plain,(
    ! [B_195,A_196] :
      ( k3_xboole_0(B_195,'#skF_4') != '#skF_2'(A_196,B_195)
      | ~ v4_pre_topc('#skF_4',A_196)
      | v2_tex_2(B_195,A_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_502])).

tff(c_1100,plain,(
    ! [A_196] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_196,'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_196)
      | v2_tex_2('#skF_4',A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_58,c_1054])).

tff(c_1161,plain,(
    ! [A_199] :
      ( '#skF_2'(A_199,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_199)
      | v2_tex_2('#skF_4',A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1100])).

tff(c_1166,plain,(
    ! [A_200] :
      ( '#skF_2'(A_200,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_200)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_175,c_1161])).

tff(c_1169,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1166,c_34])).

tff(c_1173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_234,c_1169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.57  
% 3.47/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.57  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.47/1.57  
% 3.47/1.57  %Foreground sorts:
% 3.47/1.57  
% 3.47/1.57  
% 3.47/1.57  %Background operators:
% 3.47/1.57  
% 3.47/1.57  
% 3.47/1.57  %Foreground operators:
% 3.47/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.47/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.47/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.47/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.57  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.47/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.47/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.47/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.57  
% 3.47/1.58  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.47/1.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.47/1.58  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.47/1.58  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.47/1.58  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.47/1.58  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.47/1.58  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.47/1.58  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.47/1.58  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.47/1.58  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.58  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.58  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.58  tff(c_47, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.47/1.58  tff(c_56, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_47])).
% 3.47/1.58  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.58  tff(c_58, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 3.47/1.58  tff(c_202, plain, (![A_86, B_87]: (r1_tarski('#skF_2'(A_86, B_87), B_87) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.58  tff(c_219, plain, (![A_88]: (r1_tarski('#skF_2'(A_88, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_58, c_202])).
% 3.47/1.58  tff(c_10, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.58  tff(c_75, plain, (![A_5]: (A_5='#skF_4' | ~r1_tarski(A_5, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_10])).
% 3.47/1.58  tff(c_228, plain, (![A_89]: ('#skF_2'(A_89, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_219, c_75])).
% 3.47/1.58  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.58  tff(c_231, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_228, c_34])).
% 3.47/1.58  tff(c_234, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_231])).
% 3.47/1.58  tff(c_158, plain, (![B_76, A_77]: (v4_pre_topc(B_76, A_77) | ~v1_xboole_0(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.58  tff(c_170, plain, (![A_77]: (v4_pre_topc('#skF_4', A_77) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(resolution, [status(thm)], [c_58, c_158])).
% 3.47/1.58  tff(c_175, plain, (![A_77]: (v4_pre_topc('#skF_4', A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_170])).
% 3.47/1.58  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.47/1.58  tff(c_59, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8])).
% 3.47/1.58  tff(c_83, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.58  tff(c_87, plain, (![A_4]: (k3_xboole_0('#skF_4', A_4)='#skF_4')), inference(resolution, [status(thm)], [c_59, c_83])).
% 3.47/1.58  tff(c_100, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.47/1.58  tff(c_103, plain, (![A_12, B_61]: (k9_subset_1(A_12, B_61, '#skF_4')=k3_xboole_0(B_61, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_100])).
% 3.47/1.58  tff(c_493, plain, (![A_130, B_131, D_132]: (k9_subset_1(u1_struct_0(A_130), B_131, D_132)!='#skF_2'(A_130, B_131) | ~v4_pre_topc(D_132, A_130) | ~m1_subset_1(D_132, k1_zfmisc_1(u1_struct_0(A_130))) | v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.58  tff(c_502, plain, (![B_61, A_130]: (k3_xboole_0(B_61, '#skF_4')!='#skF_2'(A_130, B_61) | ~v4_pre_topc('#skF_4', A_130) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_130))) | v2_tex_2(B_61, A_130) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(superposition, [status(thm), theory('equality')], [c_103, c_493])).
% 3.47/1.58  tff(c_1054, plain, (![B_195, A_196]: (k3_xboole_0(B_195, '#skF_4')!='#skF_2'(A_196, B_195) | ~v4_pre_topc('#skF_4', A_196) | v2_tex_2(B_195, A_196) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_502])).
% 3.47/1.58  tff(c_1100, plain, (![A_196]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_196, '#skF_4') | ~v4_pre_topc('#skF_4', A_196) | v2_tex_2('#skF_4', A_196) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_58, c_1054])).
% 3.47/1.58  tff(c_1161, plain, (![A_199]: ('#skF_2'(A_199, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_199) | v2_tex_2('#skF_4', A_199) | ~l1_pre_topc(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1100])).
% 3.47/1.58  tff(c_1166, plain, (![A_200]: ('#skF_2'(A_200, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_200) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200))), inference(resolution, [status(thm)], [c_175, c_1161])).
% 3.47/1.58  tff(c_1169, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1166, c_34])).
% 3.47/1.58  tff(c_1173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_234, c_1169])).
% 3.47/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.59  
% 3.47/1.59  Inference rules
% 3.47/1.59  ----------------------
% 3.47/1.59  #Ref     : 0
% 3.47/1.59  #Sup     : 276
% 3.47/1.59  #Fact    : 0
% 3.47/1.59  #Define  : 0
% 3.47/1.59  #Split   : 0
% 3.47/1.59  #Chain   : 0
% 3.47/1.59  #Close   : 0
% 3.47/1.59  
% 3.47/1.59  Ordering : KBO
% 3.47/1.59  
% 3.47/1.59  Simplification rules
% 3.47/1.59  ----------------------
% 3.47/1.59  #Subsume      : 47
% 3.47/1.59  #Demod        : 118
% 3.47/1.59  #Tautology    : 66
% 3.47/1.59  #SimpNegUnit  : 19
% 3.47/1.59  #BackRed      : 4
% 3.47/1.59  
% 3.47/1.59  #Partial instantiations: 0
% 3.47/1.59  #Strategies tried      : 1
% 3.47/1.59  
% 3.47/1.59  Timing (in seconds)
% 3.47/1.59  ----------------------
% 3.47/1.59  Preprocessing        : 0.30
% 3.47/1.59  Parsing              : 0.16
% 3.47/1.59  CNF conversion       : 0.02
% 3.47/1.59  Main loop            : 0.45
% 3.47/1.59  Inferencing          : 0.17
% 3.47/1.59  Reduction            : 0.13
% 3.47/1.59  Demodulation         : 0.09
% 3.47/1.59  BG Simplification    : 0.03
% 3.47/1.59  Subsumption          : 0.09
% 3.47/1.59  Abstraction          : 0.03
% 3.47/1.59  MUC search           : 0.00
% 3.47/1.59  Cooper               : 0.00
% 3.47/1.59  Total                : 0.78
% 3.47/1.59  Index Insertion      : 0.00
% 3.47/1.59  Index Deletion       : 0.00
% 3.47/1.59  Index Matching       : 0.00
% 3.47/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
