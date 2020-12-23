%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:25 EST 2020

% Result     : Theorem 12.54s
% Output     : CNFRefutation 12.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 118 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 244 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_mcart_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_120,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_73,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_24,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_20] : m1_subset_1('#skF_6',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_621,plain,(
    ! [A_163,B_164] :
      ( r1_tarski('#skF_4'(A_163,B_164),B_164)
      | v2_tex_2(B_164,A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_701,plain,(
    ! [A_170] :
      ( r1_tarski('#skF_4'(A_170,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_84,c_621])).

tff(c_30,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_2'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_99,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_2'(A_27),A_27)
      | A_27 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_30])).

tff(c_114,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_512,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_2'(A_152),B_153)
      | ~ r1_tarski(A_152,B_153)
      | A_152 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_99,c_114])).

tff(c_14,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_130,plain,(
    ! [C_88,B_89,A_90] :
      ( ~ v1_xboole_0(C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    ! [A_10,A_90] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_90,A_10) ) ),
    inference(resolution,[status(thm)],[c_61,c_130])).

tff(c_543,plain,(
    ! [B_153,A_152] :
      ( ~ v1_xboole_0(B_153)
      | ~ r1_tarski(A_152,B_153)
      | A_152 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_512,c_136])).

tff(c_704,plain,(
    ! [A_170] :
      ( ~ v1_xboole_0('#skF_6')
      | '#skF_4'(A_170,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_701,c_543])).

tff(c_717,plain,(
    ! [A_171] :
      ( '#skF_4'(A_171,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_704])).

tff(c_50,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_720,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_717,c_50])).

tff(c_723,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_720])).

tff(c_568,plain,(
    ! [B_155,A_156] :
      ( v3_pre_topc(B_155,A_156)
      | ~ v1_xboole_0(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_588,plain,(
    ! [A_156] :
      ( v3_pre_topc('#skF_6',A_156)
      | ~ v1_xboole_0('#skF_6')
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_84,c_568])).

tff(c_599,plain,(
    ! [A_156] :
      ( v3_pre_topc('#skF_6',A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_588])).

tff(c_159,plain,(
    ! [A_94,B_95,C_96] :
      ( k9_subset_1(A_94,B_95,B_95) = B_95
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    ! [A_10,B_95] : k9_subset_1(A_10,B_95,B_95) = B_95 ),
    inference(resolution,[status(thm)],[c_61,c_159])).

tff(c_999,plain,(
    ! [A_190,B_191,D_192] :
      ( k9_subset_1(u1_struct_0(A_190),B_191,D_192) != '#skF_4'(A_190,B_191)
      | ~ v3_pre_topc(D_192,A_190)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(u1_struct_0(A_190)))
      | v2_tex_2(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46264,plain,(
    ! [A_1022,B_1023] :
      ( '#skF_4'(A_1022,B_1023) != B_1023
      | ~ v3_pre_topc(B_1023,A_1022)
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(u1_struct_0(A_1022)))
      | v2_tex_2(B_1023,A_1022)
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(u1_struct_0(A_1022)))
      | ~ l1_pre_topc(A_1022) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_999])).

tff(c_46378,plain,(
    ! [A_1022] :
      ( '#skF_4'(A_1022,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1022)
      | v2_tex_2('#skF_6',A_1022)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1022)))
      | ~ l1_pre_topc(A_1022) ) ),
    inference(resolution,[status(thm)],[c_84,c_46264])).

tff(c_46430,plain,(
    ! [A_1024] :
      ( '#skF_4'(A_1024,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1024)
      | v2_tex_2('#skF_6',A_1024)
      | ~ l1_pre_topc(A_1024) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46378])).

tff(c_46442,plain,(
    ! [A_1025] :
      ( '#skF_4'(A_1025,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_1025)
      | ~ l1_pre_topc(A_1025)
      | ~ v2_pre_topc(A_1025) ) ),
    inference(resolution,[status(thm)],[c_599,c_46430])).

tff(c_46445,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46442,c_50])).

tff(c_46449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_723,c_46445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.54/5.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.54/5.66  
% 12.54/5.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.54/5.67  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_mcart_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 12.54/5.67  
% 12.54/5.67  %Foreground sorts:
% 12.54/5.67  
% 12.54/5.67  
% 12.54/5.67  %Background operators:
% 12.54/5.67  
% 12.54/5.67  
% 12.54/5.67  %Foreground operators:
% 12.54/5.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.54/5.67  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.54/5.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.54/5.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.54/5.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.54/5.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.54/5.67  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 12.54/5.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.54/5.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.54/5.67  tff('#skF_5', type, '#skF_5': $i).
% 12.54/5.67  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 12.54/5.67  tff('#skF_6', type, '#skF_6': $i).
% 12.54/5.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.54/5.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.54/5.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.54/5.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.54/5.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.54/5.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.54/5.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.54/5.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.54/5.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.54/5.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.54/5.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.54/5.67  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.54/5.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.54/5.67  
% 12.54/5.68  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 12.54/5.68  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.54/5.68  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.54/5.68  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 12.54/5.68  tff(f_88, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 12.54/5.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.54/5.68  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.54/5.68  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 12.54/5.68  tff(f_72, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 12.54/5.68  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 12.54/5.68  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 12.54/5.68  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.54/5.68  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.54/5.68  tff(c_54, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.54/5.68  tff(c_73, plain, (![A_73]: (k1_xboole_0=A_73 | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.54/5.68  tff(c_82, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_54, c_73])).
% 12.54/5.68  tff(c_24, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.54/5.68  tff(c_84, plain, (![A_20]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24])).
% 12.54/5.68  tff(c_621, plain, (![A_163, B_164]: (r1_tarski('#skF_4'(A_163, B_164), B_164) | v2_tex_2(B_164, A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.54/5.68  tff(c_701, plain, (![A_170]: (r1_tarski('#skF_4'(A_170, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_170) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_84, c_621])).
% 12.54/5.68  tff(c_30, plain, (![A_27]: (r2_hidden('#skF_2'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.54/5.68  tff(c_99, plain, (![A_27]: (r2_hidden('#skF_2'(A_27), A_27) | A_27='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_30])).
% 12.54/5.68  tff(c_114, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.54/5.68  tff(c_512, plain, (![A_152, B_153]: (r2_hidden('#skF_2'(A_152), B_153) | ~r1_tarski(A_152, B_153) | A_152='#skF_6')), inference(resolution, [status(thm)], [c_99, c_114])).
% 12.54/5.68  tff(c_14, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.54/5.68  tff(c_16, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.54/5.68  tff(c_61, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 12.54/5.68  tff(c_130, plain, (![C_88, B_89, A_90]: (~v1_xboole_0(C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.54/5.68  tff(c_136, plain, (![A_10, A_90]: (~v1_xboole_0(A_10) | ~r2_hidden(A_90, A_10))), inference(resolution, [status(thm)], [c_61, c_130])).
% 12.54/5.68  tff(c_543, plain, (![B_153, A_152]: (~v1_xboole_0(B_153) | ~r1_tarski(A_152, B_153) | A_152='#skF_6')), inference(resolution, [status(thm)], [c_512, c_136])).
% 12.54/5.68  tff(c_704, plain, (![A_170]: (~v1_xboole_0('#skF_6') | '#skF_4'(A_170, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_170) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_701, c_543])).
% 12.54/5.68  tff(c_717, plain, (![A_171]: ('#skF_4'(A_171, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_171) | ~l1_pre_topc(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_704])).
% 12.54/5.68  tff(c_50, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.54/5.68  tff(c_720, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_717, c_50])).
% 12.54/5.68  tff(c_723, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_720])).
% 12.54/5.68  tff(c_568, plain, (![B_155, A_156]: (v3_pre_topc(B_155, A_156) | ~v1_xboole_0(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.54/5.68  tff(c_588, plain, (![A_156]: (v3_pre_topc('#skF_6', A_156) | ~v1_xboole_0('#skF_6') | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(resolution, [status(thm)], [c_84, c_568])).
% 12.54/5.68  tff(c_599, plain, (![A_156]: (v3_pre_topc('#skF_6', A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_588])).
% 12.54/5.68  tff(c_159, plain, (![A_94, B_95, C_96]: (k9_subset_1(A_94, B_95, B_95)=B_95 | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.54/5.68  tff(c_165, plain, (![A_10, B_95]: (k9_subset_1(A_10, B_95, B_95)=B_95)), inference(resolution, [status(thm)], [c_61, c_159])).
% 12.54/5.68  tff(c_999, plain, (![A_190, B_191, D_192]: (k9_subset_1(u1_struct_0(A_190), B_191, D_192)!='#skF_4'(A_190, B_191) | ~v3_pre_topc(D_192, A_190) | ~m1_subset_1(D_192, k1_zfmisc_1(u1_struct_0(A_190))) | v2_tex_2(B_191, A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.54/5.68  tff(c_46264, plain, (![A_1022, B_1023]: ('#skF_4'(A_1022, B_1023)!=B_1023 | ~v3_pre_topc(B_1023, A_1022) | ~m1_subset_1(B_1023, k1_zfmisc_1(u1_struct_0(A_1022))) | v2_tex_2(B_1023, A_1022) | ~m1_subset_1(B_1023, k1_zfmisc_1(u1_struct_0(A_1022))) | ~l1_pre_topc(A_1022))), inference(superposition, [status(thm), theory('equality')], [c_165, c_999])).
% 12.54/5.68  tff(c_46378, plain, (![A_1022]: ('#skF_4'(A_1022, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1022) | v2_tex_2('#skF_6', A_1022) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1022))) | ~l1_pre_topc(A_1022))), inference(resolution, [status(thm)], [c_84, c_46264])).
% 12.54/5.68  tff(c_46430, plain, (![A_1024]: ('#skF_4'(A_1024, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1024) | v2_tex_2('#skF_6', A_1024) | ~l1_pre_topc(A_1024))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46378])).
% 12.54/5.68  tff(c_46442, plain, (![A_1025]: ('#skF_4'(A_1025, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_1025) | ~l1_pre_topc(A_1025) | ~v2_pre_topc(A_1025))), inference(resolution, [status(thm)], [c_599, c_46430])).
% 12.54/5.68  tff(c_46445, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46442, c_50])).
% 12.54/5.68  tff(c_46449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_723, c_46445])).
% 12.54/5.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.54/5.68  
% 12.54/5.68  Inference rules
% 12.54/5.68  ----------------------
% 12.54/5.68  #Ref     : 0
% 12.54/5.68  #Sup     : 12311
% 12.54/5.68  #Fact    : 0
% 12.54/5.68  #Define  : 0
% 12.54/5.68  #Split   : 35
% 12.54/5.68  #Chain   : 0
% 12.54/5.68  #Close   : 0
% 12.54/5.68  
% 12.54/5.68  Ordering : KBO
% 12.54/5.68  
% 12.54/5.68  Simplification rules
% 12.54/5.68  ----------------------
% 12.54/5.68  #Subsume      : 8163
% 12.54/5.68  #Demod        : 6953
% 12.54/5.68  #Tautology    : 3803
% 12.54/5.68  #SimpNegUnit  : 53
% 12.54/5.68  #BackRed      : 24
% 12.54/5.68  
% 12.54/5.68  #Partial instantiations: 0
% 12.54/5.68  #Strategies tried      : 1
% 12.54/5.68  
% 12.54/5.68  Timing (in seconds)
% 12.54/5.68  ----------------------
% 12.54/5.68  Preprocessing        : 0.33
% 12.54/5.68  Parsing              : 0.18
% 12.54/5.68  CNF conversion       : 0.02
% 12.54/5.68  Main loop            : 4.57
% 12.54/5.68  Inferencing          : 1.10
% 12.54/5.68  Reduction            : 1.27
% 12.54/5.68  Demodulation         : 0.88
% 12.54/5.68  BG Simplification    : 0.11
% 12.54/5.68  Subsumption          : 1.84
% 12.54/5.68  Abstraction          : 0.17
% 12.54/5.68  MUC search           : 0.00
% 12.54/5.68  Cooper               : 0.00
% 12.54/5.68  Total                : 4.93
% 12.54/5.68  Index Insertion      : 0.00
% 12.54/5.68  Index Deletion       : 0.00
% 12.54/5.68  Index Matching       : 0.00
% 12.54/5.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
