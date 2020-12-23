%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:25 EST 2020

% Result     : Theorem 23.95s
% Output     : CNFRefutation 24.11s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 114 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 239 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_113,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_71,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_82,plain,(
    ! [A_24] : m1_subset_1('#skF_6',k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_26])).

tff(c_641,plain,(
    ! [A_142,B_143] :
      ( r1_tarski('#skF_4'(A_142,B_143),B_143)
      | v2_tex_2(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1906,plain,(
    ! [A_228] :
      ( r1_tarski('#skF_4'(A_228,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_228)
      | ~ l1_pre_topc(A_228) ) ),
    inference(resolution,[status(thm)],[c_82,c_641])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_170,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ v1_xboole_0(C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_194,plain,(
    ! [B_92,A_93,A_94] :
      ( ~ v1_xboole_0(B_92)
      | ~ r2_hidden(A_93,A_94)
      | ~ r1_tarski(A_94,B_92) ) ),
    inference(resolution,[status(thm)],[c_30,c_170])).

tff(c_200,plain,(
    ! [B_92,A_1] :
      ( ~ v1_xboole_0(B_92)
      | ~ r1_tarski(A_1,B_92)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_1922,plain,(
    ! [A_228] :
      ( ~ v1_xboole_0('#skF_6')
      | v1_xboole_0('#skF_4'(A_228,'#skF_6'))
      | v2_tex_2('#skF_6',A_228)
      | ~ l1_pre_topc(A_228) ) ),
    inference(resolution,[status(thm)],[c_1906,c_200])).

tff(c_1940,plain,(
    ! [A_229] :
      ( v1_xboole_0('#skF_4'(A_229,'#skF_6'))
      | v2_tex_2('#skF_6',A_229)
      | ~ l1_pre_topc(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1922])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_1957,plain,(
    ! [A_230] :
      ( '#skF_4'(A_230,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_230)
      | ~ l1_pre_topc(A_230) ) ),
    inference(resolution,[status(thm)],[c_1940,c_76])).

tff(c_50,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1960,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1957,c_50])).

tff(c_1963,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1960])).

tff(c_497,plain,(
    ! [B_134,A_135] :
      ( v3_pre_topc(B_134,A_135)
      | ~ v1_xboole_0(B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_521,plain,(
    ! [A_135] :
      ( v3_pre_topc('#skF_6',A_135)
      | ~ v1_xboole_0('#skF_6')
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_82,c_497])).

tff(c_533,plain,(
    ! [A_135] :
      ( v3_pre_topc('#skF_6',A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_521])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_233,plain,(
    ! [A_103,B_104,C_105] :
      ( k9_subset_1(A_103,B_104,B_104) = B_104
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_242,plain,(
    ! [A_14,B_104] : k9_subset_1(A_14,B_104,B_104) = B_104 ),
    inference(resolution,[status(thm)],[c_61,c_233])).

tff(c_932,plain,(
    ! [A_165,B_166,D_167] :
      ( k9_subset_1(u1_struct_0(A_165),B_166,D_167) != '#skF_4'(A_165,B_166)
      | ~ v3_pre_topc(D_167,A_165)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0(A_165)))
      | v2_tex_2(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_66889,plain,(
    ! [A_1328,B_1329] :
      ( '#skF_4'(A_1328,B_1329) != B_1329
      | ~ v3_pre_topc(B_1329,A_1328)
      | ~ m1_subset_1(B_1329,k1_zfmisc_1(u1_struct_0(A_1328)))
      | v2_tex_2(B_1329,A_1328)
      | ~ m1_subset_1(B_1329,k1_zfmisc_1(u1_struct_0(A_1328)))
      | ~ l1_pre_topc(A_1328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_932])).

tff(c_67001,plain,(
    ! [A_1328] :
      ( '#skF_4'(A_1328,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1328)
      | v2_tex_2('#skF_6',A_1328)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1328)))
      | ~ l1_pre_topc(A_1328) ) ),
    inference(resolution,[status(thm)],[c_82,c_66889])).

tff(c_99867,plain,(
    ! [A_1665] :
      ( '#skF_4'(A_1665,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1665)
      | v2_tex_2('#skF_6',A_1665)
      | ~ l1_pre_topc(A_1665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_67001])).

tff(c_99879,plain,(
    ! [A_1666] :
      ( '#skF_4'(A_1666,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_1666)
      | ~ l1_pre_topc(A_1666)
      | ~ v2_pre_topc(A_1666) ) ),
    inference(resolution,[status(thm)],[c_533,c_99867])).

tff(c_99882,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_99879,c_50])).

tff(c_99886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1963,c_99882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.95/15.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.95/15.08  
% 23.95/15.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.95/15.08  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 23.95/15.08  
% 23.95/15.08  %Foreground sorts:
% 23.95/15.08  
% 23.95/15.08  
% 23.95/15.08  %Background operators:
% 23.95/15.08  
% 23.95/15.08  
% 23.95/15.08  %Foreground operators:
% 23.95/15.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.95/15.08  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 23.95/15.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.95/15.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.95/15.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.95/15.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.95/15.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.95/15.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.95/15.08  tff('#skF_5', type, '#skF_5': $i).
% 23.95/15.08  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 23.95/15.08  tff('#skF_6', type, '#skF_6': $i).
% 23.95/15.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.95/15.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.95/15.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.95/15.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.95/15.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 23.95/15.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.95/15.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.95/15.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.95/15.08  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.95/15.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.95/15.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.95/15.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 23.95/15.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.95/15.08  
% 24.11/15.09  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 24.11/15.09  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 24.11/15.09  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 24.11/15.09  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 24.11/15.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 24.11/15.09  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 24.11/15.09  tff(f_81, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 24.11/15.09  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 24.11/15.09  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 24.11/15.09  tff(f_50, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 24.11/15.09  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 24.11/15.09  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 24.11/15.09  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 24.11/15.09  tff(c_54, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 24.11/15.09  tff(c_71, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_42])).
% 24.11/15.09  tff(c_75, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_54, c_71])).
% 24.11/15.09  tff(c_26, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 24.11/15.09  tff(c_82, plain, (![A_24]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_26])).
% 24.11/15.09  tff(c_641, plain, (![A_142, B_143]: (r1_tarski('#skF_4'(A_142, B_143), B_143) | v2_tex_2(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_113])).
% 24.11/15.09  tff(c_1906, plain, (![A_228]: (r1_tarski('#skF_4'(A_228, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_228) | ~l1_pre_topc(A_228))), inference(resolution, [status(thm)], [c_82, c_641])).
% 24.11/15.09  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.11/15.09  tff(c_30, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 24.11/15.09  tff(c_170, plain, (![C_88, B_89, A_90]: (~v1_xboole_0(C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.11/15.09  tff(c_194, plain, (![B_92, A_93, A_94]: (~v1_xboole_0(B_92) | ~r2_hidden(A_93, A_94) | ~r1_tarski(A_94, B_92))), inference(resolution, [status(thm)], [c_30, c_170])).
% 24.11/15.09  tff(c_200, plain, (![B_92, A_1]: (~v1_xboole_0(B_92) | ~r1_tarski(A_1, B_92) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_194])).
% 24.11/15.09  tff(c_1922, plain, (![A_228]: (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4'(A_228, '#skF_6')) | v2_tex_2('#skF_6', A_228) | ~l1_pre_topc(A_228))), inference(resolution, [status(thm)], [c_1906, c_200])).
% 24.11/15.09  tff(c_1940, plain, (![A_229]: (v1_xboole_0('#skF_4'(A_229, '#skF_6')) | v2_tex_2('#skF_6', A_229) | ~l1_pre_topc(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1922])).
% 24.11/15.09  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 24.11/15.09  tff(c_76, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_12])).
% 24.11/15.09  tff(c_1957, plain, (![A_230]: ('#skF_4'(A_230, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_230) | ~l1_pre_topc(A_230))), inference(resolution, [status(thm)], [c_1940, c_76])).
% 24.11/15.09  tff(c_50, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 24.11/15.09  tff(c_1960, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1957, c_50])).
% 24.11/15.09  tff(c_1963, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1960])).
% 24.11/15.09  tff(c_497, plain, (![B_134, A_135]: (v3_pre_topc(B_134, A_135) | ~v1_xboole_0(B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.11/15.09  tff(c_521, plain, (![A_135]: (v3_pre_topc('#skF_6', A_135) | ~v1_xboole_0('#skF_6') | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(resolution, [status(thm)], [c_82, c_497])).
% 24.11/15.09  tff(c_533, plain, (![A_135]: (v3_pre_topc('#skF_6', A_135) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_521])).
% 24.11/15.09  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 24.11/15.09  tff(c_18, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.11/15.09  tff(c_61, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 24.11/15.09  tff(c_233, plain, (![A_103, B_104, C_105]: (k9_subset_1(A_103, B_104, B_104)=B_104 | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 24.11/15.09  tff(c_242, plain, (![A_14, B_104]: (k9_subset_1(A_14, B_104, B_104)=B_104)), inference(resolution, [status(thm)], [c_61, c_233])).
% 24.11/15.09  tff(c_932, plain, (![A_165, B_166, D_167]: (k9_subset_1(u1_struct_0(A_165), B_166, D_167)!='#skF_4'(A_165, B_166) | ~v3_pre_topc(D_167, A_165) | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0(A_165))) | v2_tex_2(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_113])).
% 24.11/15.09  tff(c_66889, plain, (![A_1328, B_1329]: ('#skF_4'(A_1328, B_1329)!=B_1329 | ~v3_pre_topc(B_1329, A_1328) | ~m1_subset_1(B_1329, k1_zfmisc_1(u1_struct_0(A_1328))) | v2_tex_2(B_1329, A_1328) | ~m1_subset_1(B_1329, k1_zfmisc_1(u1_struct_0(A_1328))) | ~l1_pre_topc(A_1328))), inference(superposition, [status(thm), theory('equality')], [c_242, c_932])).
% 24.11/15.09  tff(c_67001, plain, (![A_1328]: ('#skF_4'(A_1328, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1328) | v2_tex_2('#skF_6', A_1328) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1328))) | ~l1_pre_topc(A_1328))), inference(resolution, [status(thm)], [c_82, c_66889])).
% 24.11/15.09  tff(c_99867, plain, (![A_1665]: ('#skF_4'(A_1665, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1665) | v2_tex_2('#skF_6', A_1665) | ~l1_pre_topc(A_1665))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_67001])).
% 24.11/15.09  tff(c_99879, plain, (![A_1666]: ('#skF_4'(A_1666, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_1666) | ~l1_pre_topc(A_1666) | ~v2_pre_topc(A_1666))), inference(resolution, [status(thm)], [c_533, c_99867])).
% 24.11/15.09  tff(c_99882, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_99879, c_50])).
% 24.11/15.09  tff(c_99886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1963, c_99882])).
% 24.11/15.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.11/15.09  
% 24.11/15.09  Inference rules
% 24.11/15.09  ----------------------
% 24.11/15.09  #Ref     : 0
% 24.11/15.09  #Sup     : 25606
% 24.11/15.09  #Fact    : 0
% 24.11/15.09  #Define  : 0
% 24.11/15.09  #Split   : 15
% 24.11/15.09  #Chain   : 0
% 24.11/15.09  #Close   : 0
% 24.11/15.09  
% 24.11/15.09  Ordering : KBO
% 24.11/15.09  
% 24.11/15.09  Simplification rules
% 24.11/15.09  ----------------------
% 24.11/15.09  #Subsume      : 9063
% 24.11/15.09  #Demod        : 15616
% 24.11/15.09  #Tautology    : 6734
% 24.11/15.09  #SimpNegUnit  : 207
% 24.11/15.09  #BackRed      : 93
% 24.11/15.09  
% 24.11/15.09  #Partial instantiations: 0
% 24.11/15.09  #Strategies tried      : 1
% 24.11/15.09  
% 24.11/15.09  Timing (in seconds)
% 24.11/15.09  ----------------------
% 24.11/15.10  Preprocessing        : 0.33
% 24.11/15.10  Parsing              : 0.17
% 24.11/15.10  CNF conversion       : 0.02
% 24.11/15.10  Main loop            : 13.98
% 24.11/15.10  Inferencing          : 2.21
% 24.11/15.10  Reduction            : 3.64
% 24.11/15.10  Demodulation         : 2.66
% 24.11/15.10  BG Simplification    : 0.26
% 24.11/15.10  Subsumption          : 7.01
% 24.11/15.10  Abstraction          : 0.41
% 24.11/15.10  MUC search           : 0.00
% 24.11/15.10  Cooper               : 0.00
% 24.11/15.10  Total                : 14.34
% 24.11/15.10  Index Insertion      : 0.00
% 24.11/15.10  Index Deletion       : 0.00
% 24.11/15.10  Index Matching       : 0.00
% 24.11/15.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
