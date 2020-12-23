%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:30 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 167 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 385 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_5') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_124,plain,(
    ! [A_66,B_67] :
      ( r1_tarski('#skF_3'(A_66,B_67),B_67)
      | v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    ! [A_68] :
      ( r1_tarski('#skF_3'(A_68,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k2_xboole_0(A_2,B_3) = B_3
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [A_68] :
      ( k2_xboole_0('#skF_3'(A_68,'#skF_5'),'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_150,plain,(
    ! [A_71] :
      ( '#skF_3'(A_71,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_136])).

tff(c_153,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_32])).

tff(c_156,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_40,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_139,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1('#skF_3'(A_69,B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [B_16,A_14] :
      ( v4_pre_topc(B_16,A_14)
      | ~ v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_234,plain,(
    ! [A_86,B_87] :
      ( v4_pre_topc('#skF_3'(A_86,B_87),A_86)
      | ~ v1_xboole_0('#skF_3'(A_86,B_87))
      | ~ v2_pre_topc(A_86)
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_139,c_18])).

tff(c_249,plain,(
    ! [A_88] :
      ( v4_pre_topc('#skF_3'(A_88,'#skF_5'),A_88)
      | ~ v1_xboole_0('#skF_3'(A_88,'#skF_5'))
      | ~ v2_pre_topc(A_88)
      | v2_tex_2('#skF_5',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_56,c_234])).

tff(c_252,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_249])).

tff(c_254,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_36,c_156,c_252])).

tff(c_255,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_254])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,B_52) = B_52
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_51,B_52] : k9_subset_1(A_51,B_52,B_52) = B_52 ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_256,plain,(
    ! [A_89,B_90,D_91] :
      ( k9_subset_1(u1_struct_0(A_89),B_90,D_91) != '#skF_3'(A_89,B_90)
      | ~ v4_pre_topc(D_91,A_89)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(u1_struct_0(A_89)))
      | v2_tex_2(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_260,plain,(
    ! [A_92,B_93] :
      ( '#skF_3'(A_92,B_93) != B_93
      | ~ v4_pre_topc(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_256])).

tff(c_267,plain,(
    ! [A_92] :
      ( '#skF_3'(A_92,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_92)
      | v2_tex_2('#skF_5',A_92)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_56,c_260])).

tff(c_279,plain,(
    ! [A_94] :
      ( '#skF_3'(A_94,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_94)
      | v2_tex_2('#skF_5',A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_267])).

tff(c_282,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_255,c_279])).

tff(c_288,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_156,c_282])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.30  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.20/1.30  
% 2.20/1.30  %Foreground sorts:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Background operators:
% 2.20/1.30  
% 2.20/1.30  
% 2.20/1.30  %Foreground operators:
% 2.20/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.20/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.30  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.20/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.20/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.30  
% 2.20/1.31  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.20/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.20/1.31  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.20/1.31  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.20/1.31  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.20/1.31  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.20/1.31  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.20/1.31  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.20/1.31  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.20/1.31  tff(c_32, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.20/1.31  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.20/1.31  tff(c_36, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.20/1.31  tff(c_45, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.20/1.31  tff(c_54, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36, c_45])).
% 2.20/1.31  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.20/1.31  tff(c_63, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_5')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 2.20/1.31  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.31  tff(c_56, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14])).
% 2.20/1.31  tff(c_124, plain, (![A_66, B_67]: (r1_tarski('#skF_3'(A_66, B_67), B_67) | v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.31  tff(c_133, plain, (![A_68]: (r1_tarski('#skF_3'(A_68, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.20/1.31  tff(c_6, plain, (![A_2, B_3]: (k2_xboole_0(A_2, B_3)=B_3 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.20/1.31  tff(c_136, plain, (![A_68]: (k2_xboole_0('#skF_3'(A_68, '#skF_5'), '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_133, c_6])).
% 2.20/1.31  tff(c_150, plain, (![A_71]: ('#skF_3'(A_71, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_71) | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_136])).
% 2.20/1.31  tff(c_153, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_150, c_32])).
% 2.20/1.31  tff(c_156, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_153])).
% 2.20/1.31  tff(c_40, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.20/1.31  tff(c_139, plain, (![A_69, B_70]: (m1_subset_1('#skF_3'(A_69, B_70), k1_zfmisc_1(u1_struct_0(A_69))) | v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.31  tff(c_18, plain, (![B_16, A_14]: (v4_pre_topc(B_16, A_14) | ~v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.20/1.31  tff(c_234, plain, (![A_86, B_87]: (v4_pre_topc('#skF_3'(A_86, B_87), A_86) | ~v1_xboole_0('#skF_3'(A_86, B_87)) | ~v2_pre_topc(A_86) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_139, c_18])).
% 2.20/1.31  tff(c_249, plain, (![A_88]: (v4_pre_topc('#skF_3'(A_88, '#skF_5'), A_88) | ~v1_xboole_0('#skF_3'(A_88, '#skF_5')) | ~v2_pre_topc(A_88) | v2_tex_2('#skF_5', A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_56, c_234])).
% 2.20/1.31  tff(c_252, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_156, c_249])).
% 2.20/1.31  tff(c_254, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_36, c_156, c_252])).
% 2.20/1.31  tff(c_255, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_254])).
% 2.20/1.31  tff(c_10, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.31  tff(c_82, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, B_52)=B_52 | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.31  tff(c_88, plain, (![A_51, B_52]: (k9_subset_1(A_51, B_52, B_52)=B_52)), inference(resolution, [status(thm)], [c_10, c_82])).
% 2.20/1.31  tff(c_256, plain, (![A_89, B_90, D_91]: (k9_subset_1(u1_struct_0(A_89), B_90, D_91)!='#skF_3'(A_89, B_90) | ~v4_pre_topc(D_91, A_89) | ~m1_subset_1(D_91, k1_zfmisc_1(u1_struct_0(A_89))) | v2_tex_2(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.31  tff(c_260, plain, (![A_92, B_93]: ('#skF_3'(A_92, B_93)!=B_93 | ~v4_pre_topc(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(superposition, [status(thm), theory('equality')], [c_88, c_256])).
% 2.20/1.31  tff(c_267, plain, (![A_92]: ('#skF_3'(A_92, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_92) | v2_tex_2('#skF_5', A_92) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_56, c_260])).
% 2.20/1.31  tff(c_279, plain, (![A_94]: ('#skF_3'(A_94, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_94) | v2_tex_2('#skF_5', A_94) | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_267])).
% 2.20/1.31  tff(c_282, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_255, c_279])).
% 2.20/1.31  tff(c_288, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_156, c_282])).
% 2.20/1.31  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_288])).
% 2.20/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  Inference rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Ref     : 0
% 2.20/1.31  #Sup     : 52
% 2.20/1.31  #Fact    : 0
% 2.20/1.31  #Define  : 0
% 2.20/1.31  #Split   : 0
% 2.20/1.31  #Chain   : 0
% 2.20/1.31  #Close   : 0
% 2.20/1.31  
% 2.20/1.31  Ordering : KBO
% 2.20/1.31  
% 2.20/1.31  Simplification rules
% 2.20/1.31  ----------------------
% 2.20/1.31  #Subsume      : 2
% 2.20/1.31  #Demod        : 27
% 2.20/1.31  #Tautology    : 16
% 2.20/1.31  #SimpNegUnit  : 5
% 2.20/1.31  #BackRed      : 3
% 2.20/1.31  
% 2.20/1.31  #Partial instantiations: 0
% 2.20/1.31  #Strategies tried      : 1
% 2.20/1.31  
% 2.20/1.31  Timing (in seconds)
% 2.20/1.31  ----------------------
% 2.20/1.32  Preprocessing        : 0.31
% 2.20/1.32  Parsing              : 0.18
% 2.20/1.32  CNF conversion       : 0.02
% 2.20/1.32  Main loop            : 0.23
% 2.55/1.32  Inferencing          : 0.09
% 2.55/1.32  Reduction            : 0.07
% 2.55/1.32  Demodulation         : 0.05
% 2.55/1.32  BG Simplification    : 0.02
% 2.55/1.32  Subsumption          : 0.04
% 2.55/1.32  Abstraction          : 0.01
% 2.55/1.32  MUC search           : 0.00
% 2.55/1.32  Cooper               : 0.00
% 2.55/1.32  Total                : 0.58
% 2.55/1.32  Index Insertion      : 0.00
% 2.55/1.32  Index Deletion       : 0.00
% 2.55/1.32  Index Matching       : 0.00
% 2.55/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
