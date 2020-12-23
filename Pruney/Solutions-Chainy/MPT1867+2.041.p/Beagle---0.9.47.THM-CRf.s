%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:27 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 278 expanded)
%              Number of leaves         :   31 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  133 ( 663 expanded)
%              Number of equality atoms :   20 (  76 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_73,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_100,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ v1_xboole_0(B_66)
      | ~ v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_71,c_90])).

tff(c_107,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_116,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_235,plain,(
    ! [A_98,B_99] :
      ( r1_tarski('#skF_4'(A_98,B_99),B_99)
      | v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_248,plain,(
    ! [A_100] :
      ( r1_tarski('#skF_4'(A_100,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_118,c_235])).

tff(c_78,plain,(
    ! [B_56,A_55] :
      ( B_56 = A_55
      | ~ r1_tarski(B_56,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_256,plain,(
    ! [A_100] :
      ( '#skF_4'(A_100,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_248,c_78])).

tff(c_277,plain,(
    ! [A_102] :
      ( '#skF_4'(A_102,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_256])).

tff(c_280,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_277,c_40])).

tff(c_283,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_280])).

tff(c_48,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_376,plain,(
    ! [A_110,B_111] :
      ( m1_subset_1('#skF_4'(A_110,B_111),k1_zfmisc_1(u1_struct_0(A_110)))
      | v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [B_21,A_19] :
      ( v4_pre_topc(B_21,A_19)
      | ~ v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_856,plain,(
    ! [A_166,B_167] :
      ( v4_pre_topc('#skF_4'(A_166,B_167),A_166)
      | ~ v1_xboole_0('#skF_4'(A_166,B_167))
      | ~ v2_pre_topc(A_166)
      | v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_376,c_26])).

tff(c_870,plain,(
    ! [A_168] :
      ( v4_pre_topc('#skF_4'(A_168,'#skF_6'),A_168)
      | ~ v1_xboole_0('#skF_4'(A_168,'#skF_6'))
      | ~ v2_pre_topc(A_168)
      | v2_tex_2('#skF_6',A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_118,c_856])).

tff(c_879,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_870])).

tff(c_881,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_44,c_283,c_879])).

tff(c_882,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_881])).

tff(c_133,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,B_72) = B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_136,plain,(
    ! [A_15,B_72] : k9_subset_1(A_15,B_72,B_72) = B_72 ),
    inference(resolution,[status(thm)],[c_118,c_133])).

tff(c_478,plain,(
    ! [A_123,B_124,D_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,D_125) != '#skF_4'(A_123,B_124)
      | ~ v4_pre_topc(D_125,A_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_928,plain,(
    ! [A_178,B_179] :
      ( '#skF_4'(A_178,B_179) != B_179
      | ~ v4_pre_topc(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | v2_tex_2(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_478])).

tff(c_937,plain,(
    ! [A_178] :
      ( '#skF_4'(A_178,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_178)
      | v2_tex_2('#skF_6',A_178)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_118,c_928])).

tff(c_944,plain,(
    ! [A_180] :
      ( '#skF_4'(A_180,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_180)
      | v2_tex_2('#skF_6',A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_937])).

tff(c_947,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_882,c_944])).

tff(c_953,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_283,c_947])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.53  
% 3.31/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.53  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.31/1.53  
% 3.31/1.53  %Foreground sorts:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Background operators:
% 3.31/1.53  
% 3.31/1.53  
% 3.31/1.53  %Foreground operators:
% 3.31/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.31/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.53  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.31/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.31/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.31/1.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.31/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.53  
% 3.56/1.55  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.56/1.55  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.56/1.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.56/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.56/1.55  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.55  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.56/1.55  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.56/1.55  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.56/1.55  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 3.56/1.55  tff(c_40, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.56/1.55  tff(c_46, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.56/1.55  tff(c_44, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.56/1.55  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.55  tff(c_61, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.56/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.55  tff(c_71, plain, (![A_55, B_56]: (~v1_xboole_0(A_55) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_61, c_2])).
% 3.56/1.55  tff(c_73, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.55  tff(c_90, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_71, c_73])).
% 3.56/1.55  tff(c_100, plain, (![B_66, A_67]: (B_66=A_67 | ~v1_xboole_0(B_66) | ~v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_71, c_90])).
% 3.56/1.55  tff(c_107, plain, (![A_68]: (k1_xboole_0=A_68 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_12, c_100])).
% 3.56/1.55  tff(c_116, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_44, c_107])).
% 3.56/1.55  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.55  tff(c_118, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_22])).
% 3.56/1.55  tff(c_235, plain, (![A_98, B_99]: (r1_tarski('#skF_4'(A_98, B_99), B_99) | v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.55  tff(c_248, plain, (![A_100]: (r1_tarski('#skF_4'(A_100, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_118, c_235])).
% 3.56/1.55  tff(c_78, plain, (![B_56, A_55]: (B_56=A_55 | ~r1_tarski(B_56, A_55) | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_71, c_73])).
% 3.56/1.55  tff(c_256, plain, (![A_100]: ('#skF_4'(A_100, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_248, c_78])).
% 3.56/1.55  tff(c_277, plain, (![A_102]: ('#skF_4'(A_102, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_102) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_256])).
% 3.56/1.55  tff(c_280, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_277, c_40])).
% 3.56/1.55  tff(c_283, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_280])).
% 3.56/1.55  tff(c_48, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.56/1.55  tff(c_376, plain, (![A_110, B_111]: (m1_subset_1('#skF_4'(A_110, B_111), k1_zfmisc_1(u1_struct_0(A_110))) | v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.55  tff(c_26, plain, (![B_21, A_19]: (v4_pre_topc(B_21, A_19) | ~v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.55  tff(c_856, plain, (![A_166, B_167]: (v4_pre_topc('#skF_4'(A_166, B_167), A_166) | ~v1_xboole_0('#skF_4'(A_166, B_167)) | ~v2_pre_topc(A_166) | v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_376, c_26])).
% 3.56/1.55  tff(c_870, plain, (![A_168]: (v4_pre_topc('#skF_4'(A_168, '#skF_6'), A_168) | ~v1_xboole_0('#skF_4'(A_168, '#skF_6')) | ~v2_pre_topc(A_168) | v2_tex_2('#skF_6', A_168) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_118, c_856])).
% 3.56/1.55  tff(c_879, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_283, c_870])).
% 3.56/1.55  tff(c_881, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_44, c_283, c_879])).
% 3.56/1.55  tff(c_882, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_881])).
% 3.56/1.55  tff(c_133, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, B_72)=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.55  tff(c_136, plain, (![A_15, B_72]: (k9_subset_1(A_15, B_72, B_72)=B_72)), inference(resolution, [status(thm)], [c_118, c_133])).
% 3.56/1.55  tff(c_478, plain, (![A_123, B_124, D_125]: (k9_subset_1(u1_struct_0(A_123), B_124, D_125)!='#skF_4'(A_123, B_124) | ~v4_pre_topc(D_125, A_123) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.55  tff(c_928, plain, (![A_178, B_179]: ('#skF_4'(A_178, B_179)!=B_179 | ~v4_pre_topc(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | v2_tex_2(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(superposition, [status(thm), theory('equality')], [c_136, c_478])).
% 3.56/1.55  tff(c_937, plain, (![A_178]: ('#skF_4'(A_178, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_178) | v2_tex_2('#skF_6', A_178) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_118, c_928])).
% 3.56/1.55  tff(c_944, plain, (![A_180]: ('#skF_4'(A_180, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_180) | v2_tex_2('#skF_6', A_180) | ~l1_pre_topc(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_937])).
% 3.56/1.55  tff(c_947, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_882, c_944])).
% 3.56/1.55  tff(c_953, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_283, c_947])).
% 3.56/1.55  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_953])).
% 3.56/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.55  
% 3.56/1.55  Inference rules
% 3.56/1.55  ----------------------
% 3.56/1.55  #Ref     : 0
% 3.56/1.55  #Sup     : 202
% 3.56/1.55  #Fact    : 2
% 3.56/1.55  #Define  : 0
% 3.56/1.55  #Split   : 1
% 3.56/1.55  #Chain   : 0
% 3.56/1.55  #Close   : 0
% 3.56/1.55  
% 3.56/1.55  Ordering : KBO
% 3.56/1.55  
% 3.56/1.55  Simplification rules
% 3.56/1.55  ----------------------
% 3.56/1.55  #Subsume      : 87
% 3.56/1.55  #Demod        : 72
% 3.56/1.55  #Tautology    : 47
% 3.56/1.55  #SimpNegUnit  : 22
% 3.56/1.55  #BackRed      : 10
% 3.56/1.55  
% 3.56/1.55  #Partial instantiations: 0
% 3.56/1.55  #Strategies tried      : 1
% 3.56/1.55  
% 3.56/1.55  Timing (in seconds)
% 3.56/1.55  ----------------------
% 3.59/1.55  Preprocessing        : 0.32
% 3.59/1.55  Parsing              : 0.17
% 3.59/1.55  CNF conversion       : 0.03
% 3.59/1.55  Main loop            : 0.45
% 3.59/1.55  Inferencing          : 0.17
% 3.59/1.55  Reduction            : 0.12
% 3.59/1.55  Demodulation         : 0.08
% 3.59/1.55  BG Simplification    : 0.02
% 3.59/1.55  Subsumption          : 0.10
% 3.59/1.55  Abstraction          : 0.02
% 3.59/1.55  MUC search           : 0.00
% 3.59/1.55  Cooper               : 0.00
% 3.59/1.55  Total                : 0.80
% 3.59/1.55  Index Insertion      : 0.00
% 3.59/1.55  Index Deletion       : 0.00
% 3.59/1.55  Index Matching       : 0.00
% 3.59/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
