%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 124 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 264 expanded)
%              Number of equality atoms :   21 (  49 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_94,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_107,plain,(
    ! [A_60,B_61] :
      ( r1_tarski('#skF_2'(A_60,B_61),B_61)
      | v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113,plain,(
    ! [A_63] :
      ( r1_tarski('#skF_2'(A_63,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_49,c_107])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_43,c_6])).

tff(c_118,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_113,c_58])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_121,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_28])).

tff(c_124,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_121])).

tff(c_99,plain,(
    ! [B_58,A_59] :
      ( v3_pre_topc(B_58,A_59)
      | ~ v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    ! [A_59] :
      ( v3_pre_topc('#skF_4',A_59)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_49,c_99])).

tff(c_106,plain,(
    ! [A_59] :
      ( v3_pre_topc('#skF_4',A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_103])).

tff(c_60,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [B_46] : k3_xboole_0('#skF_4',B_46) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_58])).

tff(c_85,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_8,B_52] : k9_subset_1(A_8,B_52,'#skF_4') = k3_xboole_0(B_52,'#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_85])).

tff(c_180,plain,(
    ! [A_76,B_77,D_78] :
      ( k9_subset_1(u1_struct_0(A_76),B_77,D_78) != '#skF_2'(A_76,B_77)
      | ~ v3_pre_topc(D_78,A_76)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_183,plain,(
    ! [B_52,A_76] :
      ( k3_xboole_0(B_52,'#skF_4') != '#skF_2'(A_76,B_52)
      | ~ v3_pre_topc('#skF_4',A_76)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_76)))
      | v2_tex_2(B_52,A_76)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_180])).

tff(c_186,plain,(
    ! [B_79,A_80] :
      ( k3_xboole_0(B_79,'#skF_4') != '#skF_2'(A_80,B_79)
      | ~ v3_pre_topc('#skF_4',A_80)
      | v2_tex_2(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_183])).

tff(c_193,plain,(
    ! [A_80] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_80,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_80)
      | v2_tex_2('#skF_4',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_49,c_186])).

tff(c_197,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_81)
      | v2_tex_2('#skF_4',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_193])).

tff(c_202,plain,(
    ! [A_82] :
      ( '#skF_2'(A_82,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_106,c_197])).

tff(c_205,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_202,c_28])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_124,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.32  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.29/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.29/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.32  
% 2.29/1.34  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.29/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.29/1.34  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.29/1.34  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.29/1.34  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.29/1.34  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.29/1.34  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.29/1.34  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.29/1.34  tff(c_36, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.29/1.34  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.29/1.34  tff(c_32, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.29/1.34  tff(c_39, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.34  tff(c_43, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.29/1.34  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.34  tff(c_49, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_10])).
% 2.29/1.34  tff(c_107, plain, (![A_60, B_61]: (r1_tarski('#skF_2'(A_60, B_61), B_61) | v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.29/1.34  tff(c_113, plain, (![A_63]: (r1_tarski('#skF_2'(A_63, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_49, c_107])).
% 2.29/1.34  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.34  tff(c_58, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_43, c_6])).
% 2.29/1.34  tff(c_118, plain, (![A_64]: ('#skF_2'(A_64, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_113, c_58])).
% 2.29/1.34  tff(c_28, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.29/1.34  tff(c_121, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_118, c_28])).
% 2.29/1.34  tff(c_124, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_121])).
% 2.29/1.34  tff(c_99, plain, (![B_58, A_59]: (v3_pre_topc(B_58, A_59) | ~v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.34  tff(c_103, plain, (![A_59]: (v3_pre_topc('#skF_4', A_59) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(resolution, [status(thm)], [c_49, c_99])).
% 2.29/1.34  tff(c_106, plain, (![A_59]: (v3_pre_topc('#skF_4', A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_103])).
% 2.29/1.34  tff(c_60, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.34  tff(c_65, plain, (![B_46]: (k3_xboole_0('#skF_4', B_46)='#skF_4')), inference(resolution, [status(thm)], [c_60, c_58])).
% 2.29/1.34  tff(c_85, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.34  tff(c_88, plain, (![A_8, B_52]: (k9_subset_1(A_8, B_52, '#skF_4')=k3_xboole_0(B_52, '#skF_4'))), inference(resolution, [status(thm)], [c_49, c_85])).
% 2.29/1.34  tff(c_180, plain, (![A_76, B_77, D_78]: (k9_subset_1(u1_struct_0(A_76), B_77, D_78)!='#skF_2'(A_76, B_77) | ~v3_pre_topc(D_78, A_76) | ~m1_subset_1(D_78, k1_zfmisc_1(u1_struct_0(A_76))) | v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.29/1.34  tff(c_183, plain, (![B_52, A_76]: (k3_xboole_0(B_52, '#skF_4')!='#skF_2'(A_76, B_52) | ~v3_pre_topc('#skF_4', A_76) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_76))) | v2_tex_2(B_52, A_76) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(superposition, [status(thm), theory('equality')], [c_88, c_180])).
% 2.29/1.34  tff(c_186, plain, (![B_79, A_80]: (k3_xboole_0(B_79, '#skF_4')!='#skF_2'(A_80, B_79) | ~v3_pre_topc('#skF_4', A_80) | v2_tex_2(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_183])).
% 2.29/1.34  tff(c_193, plain, (![A_80]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_80, '#skF_4') | ~v3_pre_topc('#skF_4', A_80) | v2_tex_2('#skF_4', A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_49, c_186])).
% 2.29/1.34  tff(c_197, plain, (![A_81]: ('#skF_2'(A_81, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_81) | v2_tex_2('#skF_4', A_81) | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_193])).
% 2.29/1.34  tff(c_202, plain, (![A_82]: ('#skF_2'(A_82, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(resolution, [status(thm)], [c_106, c_197])).
% 2.29/1.34  tff(c_205, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_202, c_28])).
% 2.29/1.34  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_124, c_205])).
% 2.29/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  Inference rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Ref     : 0
% 2.29/1.34  #Sup     : 35
% 2.29/1.34  #Fact    : 0
% 2.29/1.34  #Define  : 0
% 2.29/1.34  #Split   : 0
% 2.29/1.34  #Chain   : 0
% 2.29/1.34  #Close   : 0
% 2.29/1.34  
% 2.29/1.34  Ordering : KBO
% 2.29/1.34  
% 2.29/1.34  Simplification rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Subsume      : 1
% 2.29/1.34  #Demod        : 20
% 2.29/1.34  #Tautology    : 13
% 2.29/1.34  #SimpNegUnit  : 3
% 2.29/1.34  #BackRed      : 1
% 2.29/1.34  
% 2.29/1.34  #Partial instantiations: 0
% 2.29/1.34  #Strategies tried      : 1
% 2.29/1.34  
% 2.29/1.34  Timing (in seconds)
% 2.29/1.34  ----------------------
% 2.29/1.34  Preprocessing        : 0.33
% 2.29/1.34  Parsing              : 0.18
% 2.29/1.34  CNF conversion       : 0.02
% 2.29/1.34  Main loop            : 0.18
% 2.29/1.34  Inferencing          : 0.07
% 2.29/1.34  Reduction            : 0.05
% 2.29/1.34  Demodulation         : 0.04
% 2.29/1.34  BG Simplification    : 0.01
% 2.29/1.34  Subsumption          : 0.03
% 2.29/1.34  Abstraction          : 0.01
% 2.29/1.34  MUC search           : 0.00
% 2.29/1.34  Cooper               : 0.00
% 2.29/1.34  Total                : 0.54
% 2.29/1.34  Index Insertion      : 0.00
% 2.29/1.34  Index Deletion       : 0.00
% 2.29/1.34  Index Matching       : 0.00
% 2.29/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
