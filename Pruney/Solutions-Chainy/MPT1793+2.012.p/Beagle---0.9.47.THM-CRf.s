%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 12.46s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 859 expanded)
%              Number of leaves         :   50 ( 319 expanded)
%              Depth                    :   15
%              Number of atoms          :  456 (2932 expanded)
%              Number of equality atoms :   16 (  81 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_234,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(C))
                     => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ r2_hidden(C,B)
               => r1_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_210,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_90,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_84,plain,(
    m1_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_114,plain,(
    ! [B_133,A_134] :
      ( l1_pre_topc(B_133)
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_114])).

tff(c_120,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_117])).

tff(c_46,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22995,plain,(
    ! [A_882] :
      ( m1_subset_1('#skF_5'(A_882),k1_zfmisc_1(u1_struct_0(A_882)))
      | ~ l1_struct_0(A_882)
      | v2_struct_0(A_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22999,plain,(
    ! [A_882] :
      ( r1_tarski('#skF_5'(A_882),u1_struct_0(A_882))
      | ~ l1_struct_0(A_882)
      | v2_struct_0(A_882) ) ),
    inference(resolution,[status(thm)],[c_22995,c_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22957,plain,(
    ! [C_878,B_879,A_880] :
      ( r2_hidden(C_878,B_879)
      | ~ r2_hidden(C_878,A_880)
      | ~ r1_tarski(A_880,B_879) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22969,plain,(
    ! [A_1,B_879] :
      ( r2_hidden('#skF_1'(A_1),B_879)
      | ~ r1_tarski(A_1,B_879)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_22957])).

tff(c_23019,plain,(
    ! [A_884,B_885] :
      ( r2_hidden('#skF_1'(A_884),B_885)
      | ~ r1_tarski(A_884,B_885)
      | v1_xboole_0(A_884) ) ),
    inference(resolution,[status(thm)],[c_4,c_22957])).

tff(c_82,plain,(
    r1_xboole_0(u1_struct_0('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_105,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,B_132) = A_131
      | ~ r1_xboole_0(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,(
    k4_xboole_0(u1_struct_0('#skF_8'),'#skF_7') = u1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_105])).

tff(c_147,plain,(
    ! [D_142,B_143,A_144] :
      ( ~ r2_hidden(D_142,B_143)
      | ~ r2_hidden(D_142,k4_xboole_0(A_144,B_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_150,plain,(
    ! [D_142] :
      ( ~ r2_hidden(D_142,'#skF_7')
      | ~ r2_hidden(D_142,u1_struct_0('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_147])).

tff(c_23042,plain,(
    ! [A_886] :
      ( ~ r2_hidden('#skF_1'(A_886),'#skF_7')
      | ~ r1_tarski(A_886,u1_struct_0('#skF_8'))
      | v1_xboole_0(A_886) ) ),
    inference(resolution,[status(thm)],[c_23019,c_150])).

tff(c_23099,plain,(
    ! [A_890] :
      ( ~ r1_tarski(A_890,u1_struct_0('#skF_8'))
      | ~ r1_tarski(A_890,'#skF_7')
      | v1_xboole_0(A_890) ) ),
    inference(resolution,[status(thm)],[c_22969,c_23042])).

tff(c_23103,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22999,c_23099])).

tff(c_23114,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_23103])).

tff(c_23118,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_23114])).

tff(c_23121,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_23118])).

tff(c_23125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_23121])).

tff(c_23127,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_23114])).

tff(c_163,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_2'(A_148,B_149),A_148)
      | r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_148,B_149] :
      ( ~ v1_xboole_0(A_148)
      | r1_tarski(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_23126,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_23114])).

tff(c_23152,plain,(
    ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_23126])).

tff(c_23156,plain,(
    ~ v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_183,c_23152])).

tff(c_22443,plain,(
    ! [A_831] :
      ( m1_subset_1('#skF_5'(A_831),k1_zfmisc_1(u1_struct_0(A_831)))
      | ~ l1_struct_0(A_831)
      | v2_struct_0(A_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22447,plain,(
    ! [A_831] :
      ( r1_tarski('#skF_5'(A_831),u1_struct_0(A_831))
      | ~ l1_struct_0(A_831)
      | v2_struct_0(A_831) ) ),
    inference(resolution,[status(thm)],[c_22443,c_42])).

tff(c_257,plain,(
    ! [C_162,B_163,A_164] :
      ( r2_hidden(C_162,B_163)
      | ~ r2_hidden(C_162,A_164)
      | ~ r1_tarski(A_164,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_266,plain,(
    ! [A_1,B_163] :
      ( r2_hidden('#skF_1'(A_1),B_163)
      | ~ r1_tarski(A_1,B_163)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_267,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165),B_166)
      | ~ r1_tarski(A_165,B_166)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_4,c_257])).

tff(c_22455,plain,(
    ! [A_833] :
      ( ~ r2_hidden('#skF_1'(A_833),'#skF_7')
      | ~ r1_tarski(A_833,u1_struct_0('#skF_8'))
      | v1_xboole_0(A_833) ) ),
    inference(resolution,[status(thm)],[c_267,c_150])).

tff(c_22490,plain,(
    ! [A_835] :
      ( ~ r1_tarski(A_835,u1_struct_0('#skF_8'))
      | ~ r1_tarski(A_835,'#skF_7')
      | v1_xboole_0(A_835) ) ),
    inference(resolution,[status(thm)],[c_266,c_22455])).

tff(c_22494,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22447,c_22490])).

tff(c_22505,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22494])).

tff(c_22510,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_22505])).

tff(c_22537,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_22510])).

tff(c_22541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_22537])).

tff(c_22543,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_22505])).

tff(c_22542,plain,
    ( ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7')
    | v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_22505])).

tff(c_22544,plain,(
    ~ r1_tarski('#skF_5'('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22542])).

tff(c_22548,plain,(
    ~ v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_183,c_22544])).

tff(c_233,plain,(
    ! [D_158,A_159,B_160] :
      ( r2_hidden(D_158,A_159)
      | ~ r2_hidden(D_158,k4_xboole_0(A_159,B_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22581,plain,(
    ! [A_845,B_846] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_845,B_846)),A_845)
      | v1_xboole_0(k4_xboole_0(A_845,B_846)) ) ),
    inference(resolution,[status(thm)],[c_4,c_233])).

tff(c_155,plain,(
    ! [A_144,B_143] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_144,B_143)),B_143)
      | v1_xboole_0(k4_xboole_0(A_144,B_143)) ) ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_22647,plain,(
    ! [A_850] : v1_xboole_0(k4_xboole_0(A_850,A_850)) ),
    inference(resolution,[status(thm)],[c_22581,c_155])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_3363,plain,(
    ! [C_316,A_317,B_318] :
      ( m1_subset_1(C_316,u1_struct_0(A_317))
      | ~ m1_subset_1(C_316,u1_struct_0(B_318))
      | ~ m1_pre_topc(B_318,A_317)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3365,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_9',u1_struct_0(A_317))
      | ~ m1_pre_topc('#skF_8',A_317)
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_80,c_3363])).

tff(c_3368,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_9',u1_struct_0(A_317))
      | ~ m1_pre_topc('#skF_8',A_317)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3365])).

tff(c_156,plain,(
    ! [D_145] :
      ( ~ r2_hidden(D_145,'#skF_7')
      | ~ r2_hidden(D_145,u1_struct_0('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_147])).

tff(c_161,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_8')),'#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_184,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_290,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_267,c_184])).

tff(c_307,plain,(
    ~ r1_tarski(u1_struct_0('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_311,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_183,c_307])).

tff(c_208,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(A_156,B_157)
      | v1_xboole_0(B_157)
      | ~ m1_subset_1(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    ! [A_156] :
      ( ~ r2_hidden(A_156,'#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_8'))
      | ~ m1_subset_1(A_156,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_208,c_150])).

tff(c_478,plain,(
    ! [A_184] :
      ( ~ r2_hidden(A_184,'#skF_7')
      | ~ m1_subset_1(A_184,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_229])).

tff(c_482,plain,(
    ~ r2_hidden('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_478])).

tff(c_92,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_88,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_74,plain,(
    ! [A_43,B_47,C_49] :
      ( r1_tmap_1(A_43,k6_tmap_1(A_43,B_47),k7_tmap_1(A_43,B_47),C_49)
      | r2_hidden(C_49,B_47)
      | ~ m1_subset_1(C_49,u1_struct_0(A_43))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( v1_funct_2(k7_tmap_1(A_39,B_40),u1_struct_0(A_39),u1_struct_0(k6_tmap_1(A_39,B_40)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1042,plain,(
    ! [A_221,B_222] :
      ( ~ v2_struct_0(k6_tmap_1(A_221,B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1052,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_1042])).

tff(c_1057,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1052])).

tff(c_1058,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1057])).

tff(c_1281,plain,(
    ! [A_239,B_240] :
      ( v2_pre_topc(k6_tmap_1(A_239,B_240))
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1291,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_1281])).

tff(c_1296,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_1291])).

tff(c_1297,plain,(
    v2_pre_topc(k6_tmap_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1296])).

tff(c_518,plain,(
    ! [A_186,B_187] :
      ( l1_pre_topc(k6_tmap_1(A_186,B_187))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_528,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_518])).

tff(c_533,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_528])).

tff(c_534,plain,(
    l1_pre_topc(k6_tmap_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_533])).

tff(c_932,plain,(
    ! [A_213,B_214] :
      ( v1_funct_1(k7_tmap_1(A_213,B_214))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_942,plain,
    ( v1_funct_1(k7_tmap_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_932])).

tff(c_947,plain,
    ( v1_funct_1(k7_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_942])).

tff(c_948,plain,(
    v1_funct_1(k7_tmap_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_947])).

tff(c_62,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k7_tmap_1(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(k6_tmap_1(A_39,B_40)))))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4808,plain,(
    ! [D_405,B_407,A_404,C_403,F_406] :
      ( r1_tmap_1(D_405,A_404,k2_tmap_1(B_407,A_404,C_403,D_405),F_406)
      | ~ r1_tmap_1(B_407,A_404,C_403,F_406)
      | ~ m1_subset_1(F_406,u1_struct_0(D_405))
      | ~ m1_subset_1(F_406,u1_struct_0(B_407))
      | ~ m1_pre_topc(D_405,B_407)
      | v2_struct_0(D_405)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_407),u1_struct_0(A_404))))
      | ~ v1_funct_2(C_403,u1_struct_0(B_407),u1_struct_0(A_404))
      | ~ v1_funct_1(C_403)
      | ~ l1_pre_topc(B_407)
      | ~ v2_pre_topc(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_22142,plain,(
    ! [D_820,A_821,B_822,F_823] :
      ( r1_tmap_1(D_820,k6_tmap_1(A_821,B_822),k2_tmap_1(A_821,k6_tmap_1(A_821,B_822),k7_tmap_1(A_821,B_822),D_820),F_823)
      | ~ r1_tmap_1(A_821,k6_tmap_1(A_821,B_822),k7_tmap_1(A_821,B_822),F_823)
      | ~ m1_subset_1(F_823,u1_struct_0(D_820))
      | ~ m1_subset_1(F_823,u1_struct_0(A_821))
      | ~ m1_pre_topc(D_820,A_821)
      | v2_struct_0(D_820)
      | ~ v1_funct_2(k7_tmap_1(A_821,B_822),u1_struct_0(A_821),u1_struct_0(k6_tmap_1(A_821,B_822)))
      | ~ v1_funct_1(k7_tmap_1(A_821,B_822))
      | ~ l1_pre_topc(k6_tmap_1(A_821,B_822))
      | ~ v2_pre_topc(k6_tmap_1(A_821,B_822))
      | v2_struct_0(k6_tmap_1(A_821,B_822))
      | ~ m1_subset_1(B_822,k1_zfmisc_1(u1_struct_0(A_821)))
      | ~ l1_pre_topc(A_821)
      | ~ v2_pre_topc(A_821)
      | v2_struct_0(A_821) ) ),
    inference(resolution,[status(thm)],[c_62,c_4808])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_8',k6_tmap_1('#skF_6','#skF_7'),k2_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_22145,plain,
    ( ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | v2_struct_0('#skF_8')
    | ~ v1_funct_2(k7_tmap_1('#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_6','#skF_7')))
    | ~ v1_funct_1(k7_tmap_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0(k6_tmap_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_22142,c_78])).

tff(c_22148,plain,
    ( ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_8')
    | ~ v1_funct_2(k7_tmap_1('#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_6','#skF_7')))
    | v2_struct_0(k6_tmap_1('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_1297,c_534,c_948,c_84,c_80,c_22145])).

tff(c_22149,plain,
    ( ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ v1_funct_2(k7_tmap_1('#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1058,c_86,c_22148])).

tff(c_22253,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_6','#skF_7'),u1_struct_0('#skF_6'),u1_struct_0(k6_tmap_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_22149])).

tff(c_22256,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_22253])).

tff(c_22259,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_22256])).

tff(c_22261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_22259])).

tff(c_22262,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_22149])).

tff(c_22400,plain,(
    ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_6','#skF_7'),k7_tmap_1('#skF_6','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_22262])).

tff(c_22403,plain,
    ( r2_hidden('#skF_9','#skF_7')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_22400])).

tff(c_22406,plain,
    ( r2_hidden('#skF_9','#skF_7')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_22403])).

tff(c_22407,plain,(
    ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_482,c_22406])).

tff(c_22410,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3368,c_22407])).

tff(c_22413,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_84,c_22410])).

tff(c_22415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_22413])).

tff(c_22416,plain,(
    ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_22262])).

tff(c_22420,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3368,c_22416])).

tff(c_22423,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_84,c_22420])).

tff(c_22425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_22423])).

tff(c_22426,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_185,plain,(
    ! [A_150,B_151] :
      ( ~ v1_xboole_0(A_150)
      | r1_tarski(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_193,plain,(
    ! [B_152,A_153] :
      ( B_152 = A_153
      | ~ r1_tarski(B_152,A_153)
      | ~ v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_185,c_30])).

tff(c_203,plain,(
    ! [B_149,A_148] :
      ( B_149 = A_148
      | ~ v1_xboole_0(B_149)
      | ~ v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_183,c_193])).

tff(c_22430,plain,(
    ! [A_148] :
      ( u1_struct_0('#skF_8') = A_148
      | ~ v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_22426,c_203])).

tff(c_22657,plain,(
    ! [A_851] : k4_xboole_0(A_851,A_851) = u1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22647,c_22430])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22753,plain,(
    ! [D_857,A_858] :
      ( ~ r2_hidden(D_857,A_858)
      | ~ r2_hidden(D_857,u1_struct_0('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22657,c_14])).

tff(c_22813,plain,(
    ! [A_863] :
      ( ~ r2_hidden('#skF_1'(A_863),u1_struct_0('#skF_8'))
      | v1_xboole_0(A_863) ) ),
    inference(resolution,[status(thm)],[c_4,c_22753])).

tff(c_22837,plain,(
    ! [A_864] :
      ( ~ r1_tarski(A_864,u1_struct_0('#skF_8'))
      | v1_xboole_0(A_864) ) ),
    inference(resolution,[status(thm)],[c_266,c_22813])).

tff(c_22841,plain,
    ( v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22447,c_22837])).

tff(c_22852,plain,
    ( v1_xboole_0('#skF_5'('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22543,c_22841])).

tff(c_22854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22548,c_22852])).

tff(c_22855,plain,(
    v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_22542])).

tff(c_50,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_5'(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22864,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22855,c_50])).

tff(c_22869,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22543,c_22864])).

tff(c_22871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22869])).

tff(c_22872,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_22882,plain,(
    ! [D_867,A_868,B_869] :
      ( r2_hidden(D_867,A_868)
      | ~ r2_hidden(D_867,k4_xboole_0(A_868,B_869)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23191,plain,(
    ! [A_898,B_899] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_898,B_899)),A_898)
      | v1_xboole_0(k4_xboole_0(A_898,B_899)) ) ),
    inference(resolution,[status(thm)],[c_4,c_22882])).

tff(c_23228,plain,(
    ! [A_900,B_901] :
      ( ~ v1_xboole_0(A_900)
      | v1_xboole_0(k4_xboole_0(A_900,B_901)) ) ),
    inference(resolution,[status(thm)],[c_23191,c_2])).

tff(c_22874,plain,(
    ! [A_865,B_866] :
      ( ~ v1_xboole_0(A_865)
      | r1_tarski(A_865,B_866) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_22900,plain,(
    ! [B_870,A_871] :
      ( B_870 = A_871
      | ~ r1_tarski(B_870,A_871)
      | ~ v1_xboole_0(A_871) ) ),
    inference(resolution,[status(thm)],[c_22874,c_30])).

tff(c_22915,plain,(
    ! [B_873,A_874] :
      ( B_873 = A_874
      | ~ v1_xboole_0(B_873)
      | ~ v1_xboole_0(A_874) ) ),
    inference(resolution,[status(thm)],[c_183,c_22900])).

tff(c_22918,plain,(
    ! [A_874] :
      ( u1_struct_0('#skF_8') = A_874
      | ~ v1_xboole_0(A_874) ) ),
    inference(resolution,[status(thm)],[c_22872,c_22915])).

tff(c_23244,plain,(
    ! [A_902,B_903] :
      ( k4_xboole_0(A_902,B_903) = u1_struct_0('#skF_8')
      | ~ v1_xboole_0(A_902) ) ),
    inference(resolution,[status(thm)],[c_23228,c_22918])).

tff(c_23269,plain,(
    ! [B_906] : k4_xboole_0(u1_struct_0('#skF_8'),B_906) = u1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22872,c_23244])).

tff(c_23328,plain,(
    ! [D_909,B_910] :
      ( ~ r2_hidden(D_909,B_910)
      | ~ r2_hidden(D_909,u1_struct_0('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23269,c_14])).

tff(c_23373,plain,(
    ! [A_911] :
      ( ~ r2_hidden('#skF_1'(A_911),u1_struct_0('#skF_8'))
      | v1_xboole_0(A_911) ) ),
    inference(resolution,[status(thm)],[c_4,c_23328])).

tff(c_23402,plain,(
    ! [A_912] :
      ( ~ r1_tarski(A_912,u1_struct_0('#skF_8'))
      | v1_xboole_0(A_912) ) ),
    inference(resolution,[status(thm)],[c_22969,c_23373])).

tff(c_23406,plain,
    ( v1_xboole_0('#skF_5'('#skF_8'))
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_22999,c_23402])).

tff(c_23417,plain,
    ( v1_xboole_0('#skF_5'('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23127,c_23406])).

tff(c_23419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_23156,c_23417])).

tff(c_23420,plain,(
    v1_xboole_0('#skF_5'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_23126])).

tff(c_23429,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_23420,c_50])).

tff(c_23434,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23127,c_23429])).

tff(c_23436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_23434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:45:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.46/4.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.46/4.75  
% 12.46/4.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.46/4.75  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 12.46/4.75  
% 12.46/4.75  %Foreground sorts:
% 12.46/4.75  
% 12.46/4.75  
% 12.46/4.75  %Background operators:
% 12.46/4.75  
% 12.46/4.75  
% 12.46/4.75  %Foreground operators:
% 12.46/4.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.46/4.75  tff('#skF_5', type, '#skF_5': $i > $i).
% 12.46/4.75  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 12.46/4.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.46/4.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.46/4.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.46/4.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.46/4.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.46/4.75  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 12.46/4.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.46/4.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 12.46/4.75  tff('#skF_7', type, '#skF_7': $i).
% 12.46/4.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.46/4.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.46/4.75  tff('#skF_6', type, '#skF_6': $i).
% 12.46/4.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.46/4.75  tff('#skF_9', type, '#skF_9': $i).
% 12.46/4.75  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.46/4.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.46/4.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.46/4.75  tff('#skF_8', type, '#skF_8': $i).
% 12.46/4.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.46/4.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.46/4.75  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 12.46/4.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.46/4.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.46/4.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.46/4.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.46/4.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.46/4.75  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.46/4.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.46/4.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.46/4.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.46/4.75  
% 12.84/4.78  tff(f_234, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 12.84/4.78  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.84/4.78  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.84/4.78  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_struct_0)).
% 12.84/4.78  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.84/4.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.84/4.78  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.84/4.78  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.84/4.78  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.84/4.78  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 12.84/4.78  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.84/4.78  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 12.84/4.78  tff(f_136, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 12.84/4.78  tff(f_152, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 12.84/4.78  tff(f_121, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 12.84/4.78  tff(f_210, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 12.84/4.78  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.84/4.78  tff(c_86, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_90, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_84, plain, (m1_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_114, plain, (![B_133, A_134]: (l1_pre_topc(B_133) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.84/4.78  tff(c_117, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_84, c_114])).
% 12.84/4.78  tff(c_120, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_117])).
% 12.84/4.78  tff(c_46, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.84/4.78  tff(c_22995, plain, (![A_882]: (m1_subset_1('#skF_5'(A_882), k1_zfmisc_1(u1_struct_0(A_882))) | ~l1_struct_0(A_882) | v2_struct_0(A_882))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.84/4.78  tff(c_42, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.84/4.78  tff(c_22999, plain, (![A_882]: (r1_tarski('#skF_5'(A_882), u1_struct_0(A_882)) | ~l1_struct_0(A_882) | v2_struct_0(A_882))), inference(resolution, [status(thm)], [c_22995, c_42])).
% 12.84/4.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/4.78  tff(c_22957, plain, (![C_878, B_879, A_880]: (r2_hidden(C_878, B_879) | ~r2_hidden(C_878, A_880) | ~r1_tarski(A_880, B_879))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.84/4.78  tff(c_22969, plain, (![A_1, B_879]: (r2_hidden('#skF_1'(A_1), B_879) | ~r1_tarski(A_1, B_879) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_22957])).
% 12.84/4.78  tff(c_23019, plain, (![A_884, B_885]: (r2_hidden('#skF_1'(A_884), B_885) | ~r1_tarski(A_884, B_885) | v1_xboole_0(A_884))), inference(resolution, [status(thm)], [c_4, c_22957])).
% 12.84/4.78  tff(c_82, plain, (r1_xboole_0(u1_struct_0('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_105, plain, (![A_131, B_132]: (k4_xboole_0(A_131, B_132)=A_131 | ~r1_xboole_0(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.84/4.78  tff(c_109, plain, (k4_xboole_0(u1_struct_0('#skF_8'), '#skF_7')=u1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_82, c_105])).
% 12.84/4.78  tff(c_147, plain, (![D_142, B_143, A_144]: (~r2_hidden(D_142, B_143) | ~r2_hidden(D_142, k4_xboole_0(A_144, B_143)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.84/4.78  tff(c_150, plain, (![D_142]: (~r2_hidden(D_142, '#skF_7') | ~r2_hidden(D_142, u1_struct_0('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_147])).
% 12.84/4.78  tff(c_23042, plain, (![A_886]: (~r2_hidden('#skF_1'(A_886), '#skF_7') | ~r1_tarski(A_886, u1_struct_0('#skF_8')) | v1_xboole_0(A_886))), inference(resolution, [status(thm)], [c_23019, c_150])).
% 12.84/4.78  tff(c_23099, plain, (![A_890]: (~r1_tarski(A_890, u1_struct_0('#skF_8')) | ~r1_tarski(A_890, '#skF_7') | v1_xboole_0(A_890))), inference(resolution, [status(thm)], [c_22969, c_23042])).
% 12.84/4.78  tff(c_23103, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_22999, c_23099])).
% 12.84/4.78  tff(c_23114, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_86, c_23103])).
% 12.84/4.78  tff(c_23118, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_23114])).
% 12.84/4.78  tff(c_23121, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_46, c_23118])).
% 12.84/4.78  tff(c_23125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_23121])).
% 12.84/4.78  tff(c_23127, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_23114])).
% 12.84/4.78  tff(c_163, plain, (![A_148, B_149]: (r2_hidden('#skF_2'(A_148, B_149), A_148) | r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.84/4.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/4.78  tff(c_183, plain, (![A_148, B_149]: (~v1_xboole_0(A_148) | r1_tarski(A_148, B_149))), inference(resolution, [status(thm)], [c_163, c_2])).
% 12.84/4.78  tff(c_23126, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8'))), inference(splitRight, [status(thm)], [c_23114])).
% 12.84/4.78  tff(c_23152, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_23126])).
% 12.84/4.78  tff(c_23156, plain, (~v1_xboole_0('#skF_5'('#skF_8'))), inference(resolution, [status(thm)], [c_183, c_23152])).
% 12.84/4.78  tff(c_22443, plain, (![A_831]: (m1_subset_1('#skF_5'(A_831), k1_zfmisc_1(u1_struct_0(A_831))) | ~l1_struct_0(A_831) | v2_struct_0(A_831))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.84/4.78  tff(c_22447, plain, (![A_831]: (r1_tarski('#skF_5'(A_831), u1_struct_0(A_831)) | ~l1_struct_0(A_831) | v2_struct_0(A_831))), inference(resolution, [status(thm)], [c_22443, c_42])).
% 12.84/4.78  tff(c_257, plain, (![C_162, B_163, A_164]: (r2_hidden(C_162, B_163) | ~r2_hidden(C_162, A_164) | ~r1_tarski(A_164, B_163))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.84/4.78  tff(c_266, plain, (![A_1, B_163]: (r2_hidden('#skF_1'(A_1), B_163) | ~r1_tarski(A_1, B_163) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_257])).
% 12.84/4.78  tff(c_267, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(A_165), B_166) | ~r1_tarski(A_165, B_166) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_4, c_257])).
% 12.84/4.78  tff(c_22455, plain, (![A_833]: (~r2_hidden('#skF_1'(A_833), '#skF_7') | ~r1_tarski(A_833, u1_struct_0('#skF_8')) | v1_xboole_0(A_833))), inference(resolution, [status(thm)], [c_267, c_150])).
% 12.84/4.78  tff(c_22490, plain, (![A_835]: (~r1_tarski(A_835, u1_struct_0('#skF_8')) | ~r1_tarski(A_835, '#skF_7') | v1_xboole_0(A_835))), inference(resolution, [status(thm)], [c_266, c_22455])).
% 12.84/4.78  tff(c_22494, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_22447, c_22490])).
% 12.84/4.78  tff(c_22505, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_86, c_22494])).
% 12.84/4.78  tff(c_22510, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_22505])).
% 12.84/4.78  tff(c_22537, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_46, c_22510])).
% 12.84/4.78  tff(c_22541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_22537])).
% 12.84/4.78  tff(c_22543, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_22505])).
% 12.84/4.78  tff(c_22542, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7') | v1_xboole_0('#skF_5'('#skF_8'))), inference(splitRight, [status(thm)], [c_22505])).
% 12.84/4.78  tff(c_22544, plain, (~r1_tarski('#skF_5'('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_22542])).
% 12.84/4.78  tff(c_22548, plain, (~v1_xboole_0('#skF_5'('#skF_8'))), inference(resolution, [status(thm)], [c_183, c_22544])).
% 12.84/4.78  tff(c_233, plain, (![D_158, A_159, B_160]: (r2_hidden(D_158, A_159) | ~r2_hidden(D_158, k4_xboole_0(A_159, B_160)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.84/4.78  tff(c_22581, plain, (![A_845, B_846]: (r2_hidden('#skF_1'(k4_xboole_0(A_845, B_846)), A_845) | v1_xboole_0(k4_xboole_0(A_845, B_846)))), inference(resolution, [status(thm)], [c_4, c_233])).
% 12.84/4.78  tff(c_155, plain, (![A_144, B_143]: (~r2_hidden('#skF_1'(k4_xboole_0(A_144, B_143)), B_143) | v1_xboole_0(k4_xboole_0(A_144, B_143)))), inference(resolution, [status(thm)], [c_4, c_147])).
% 12.84/4.78  tff(c_22647, plain, (![A_850]: (v1_xboole_0(k4_xboole_0(A_850, A_850)))), inference(resolution, [status(thm)], [c_22581, c_155])).
% 12.84/4.78  tff(c_94, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_80, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_3363, plain, (![C_316, A_317, B_318]: (m1_subset_1(C_316, u1_struct_0(A_317)) | ~m1_subset_1(C_316, u1_struct_0(B_318)) | ~m1_pre_topc(B_318, A_317) | v2_struct_0(B_318) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.84/4.78  tff(c_3365, plain, (![A_317]: (m1_subset_1('#skF_9', u1_struct_0(A_317)) | ~m1_pre_topc('#skF_8', A_317) | v2_struct_0('#skF_8') | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_80, c_3363])).
% 12.84/4.78  tff(c_3368, plain, (![A_317]: (m1_subset_1('#skF_9', u1_struct_0(A_317)) | ~m1_pre_topc('#skF_8', A_317) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(negUnitSimplification, [status(thm)], [c_86, c_3365])).
% 12.84/4.78  tff(c_156, plain, (![D_145]: (~r2_hidden(D_145, '#skF_7') | ~r2_hidden(D_145, u1_struct_0('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_147])).
% 12.84/4.78  tff(c_161, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_8')), '#skF_7') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_156])).
% 12.84/4.78  tff(c_184, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_161])).
% 12.84/4.78  tff(c_290, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_7') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_267, c_184])).
% 12.84/4.78  tff(c_307, plain, (~r1_tarski(u1_struct_0('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_290])).
% 12.84/4.78  tff(c_311, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_183, c_307])).
% 12.84/4.78  tff(c_208, plain, (![A_156, B_157]: (r2_hidden(A_156, B_157) | v1_xboole_0(B_157) | ~m1_subset_1(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.84/4.78  tff(c_229, plain, (![A_156]: (~r2_hidden(A_156, '#skF_7') | v1_xboole_0(u1_struct_0('#skF_8')) | ~m1_subset_1(A_156, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_208, c_150])).
% 12.84/4.78  tff(c_478, plain, (![A_184]: (~r2_hidden(A_184, '#skF_7') | ~m1_subset_1(A_184, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_311, c_229])).
% 12.84/4.78  tff(c_482, plain, (~r2_hidden('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_478])).
% 12.84/4.78  tff(c_92, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_88, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_74, plain, (![A_43, B_47, C_49]: (r1_tmap_1(A_43, k6_tmap_1(A_43, B_47), k7_tmap_1(A_43, B_47), C_49) | r2_hidden(C_49, B_47) | ~m1_subset_1(C_49, u1_struct_0(A_43)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_170])).
% 12.84/4.78  tff(c_64, plain, (![A_39, B_40]: (v1_funct_2(k7_tmap_1(A_39, B_40), u1_struct_0(A_39), u1_struct_0(k6_tmap_1(A_39, B_40))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.84/4.78  tff(c_1042, plain, (![A_221, B_222]: (~v2_struct_0(k6_tmap_1(A_221, B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_152])).
% 12.84/4.78  tff(c_1052, plain, (~v2_struct_0(k6_tmap_1('#skF_6', '#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_88, c_1042])).
% 12.84/4.78  tff(c_1057, plain, (~v2_struct_0(k6_tmap_1('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1052])).
% 12.84/4.78  tff(c_1058, plain, (~v2_struct_0(k6_tmap_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_1057])).
% 12.84/4.78  tff(c_1281, plain, (![A_239, B_240]: (v2_pre_topc(k6_tmap_1(A_239, B_240)) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_152])).
% 12.84/4.78  tff(c_1291, plain, (v2_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_88, c_1281])).
% 12.84/4.78  tff(c_1296, plain, (v2_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_1291])).
% 12.84/4.78  tff(c_1297, plain, (v2_pre_topc(k6_tmap_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_1296])).
% 12.84/4.78  tff(c_518, plain, (![A_186, B_187]: (l1_pre_topc(k6_tmap_1(A_186, B_187)) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.84/4.78  tff(c_528, plain, (l1_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_88, c_518])).
% 12.84/4.78  tff(c_533, plain, (l1_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_528])).
% 12.84/4.78  tff(c_534, plain, (l1_pre_topc(k6_tmap_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_533])).
% 12.84/4.78  tff(c_932, plain, (![A_213, B_214]: (v1_funct_1(k7_tmap_1(A_213, B_214)) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.84/4.78  tff(c_942, plain, (v1_funct_1(k7_tmap_1('#skF_6', '#skF_7')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_88, c_932])).
% 12.84/4.78  tff(c_947, plain, (v1_funct_1(k7_tmap_1('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_942])).
% 12.84/4.78  tff(c_948, plain, (v1_funct_1(k7_tmap_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_947])).
% 12.84/4.78  tff(c_62, plain, (![A_39, B_40]: (m1_subset_1(k7_tmap_1(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39), u1_struct_0(k6_tmap_1(A_39, B_40))))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 12.84/4.78  tff(c_4808, plain, (![D_405, B_407, A_404, C_403, F_406]: (r1_tmap_1(D_405, A_404, k2_tmap_1(B_407, A_404, C_403, D_405), F_406) | ~r1_tmap_1(B_407, A_404, C_403, F_406) | ~m1_subset_1(F_406, u1_struct_0(D_405)) | ~m1_subset_1(F_406, u1_struct_0(B_407)) | ~m1_pre_topc(D_405, B_407) | v2_struct_0(D_405) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_407), u1_struct_0(A_404)))) | ~v1_funct_2(C_403, u1_struct_0(B_407), u1_struct_0(A_404)) | ~v1_funct_1(C_403) | ~l1_pre_topc(B_407) | ~v2_pre_topc(B_407) | v2_struct_0(B_407) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_210])).
% 12.84/4.78  tff(c_22142, plain, (![D_820, A_821, B_822, F_823]: (r1_tmap_1(D_820, k6_tmap_1(A_821, B_822), k2_tmap_1(A_821, k6_tmap_1(A_821, B_822), k7_tmap_1(A_821, B_822), D_820), F_823) | ~r1_tmap_1(A_821, k6_tmap_1(A_821, B_822), k7_tmap_1(A_821, B_822), F_823) | ~m1_subset_1(F_823, u1_struct_0(D_820)) | ~m1_subset_1(F_823, u1_struct_0(A_821)) | ~m1_pre_topc(D_820, A_821) | v2_struct_0(D_820) | ~v1_funct_2(k7_tmap_1(A_821, B_822), u1_struct_0(A_821), u1_struct_0(k6_tmap_1(A_821, B_822))) | ~v1_funct_1(k7_tmap_1(A_821, B_822)) | ~l1_pre_topc(k6_tmap_1(A_821, B_822)) | ~v2_pre_topc(k6_tmap_1(A_821, B_822)) | v2_struct_0(k6_tmap_1(A_821, B_822)) | ~m1_subset_1(B_822, k1_zfmisc_1(u1_struct_0(A_821))) | ~l1_pre_topc(A_821) | ~v2_pre_topc(A_821) | v2_struct_0(A_821))), inference(resolution, [status(thm)], [c_62, c_4808])).
% 12.84/4.78  tff(c_78, plain, (~r1_tmap_1('#skF_8', k6_tmap_1('#skF_6', '#skF_7'), k2_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_234])).
% 12.84/4.78  tff(c_22145, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~v1_funct_2(k7_tmap_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'), u1_struct_0(k6_tmap_1('#skF_6', '#skF_7'))) | ~v1_funct_1(k7_tmap_1('#skF_6', '#skF_7')) | ~l1_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | ~v2_pre_topc(k6_tmap_1('#skF_6', '#skF_7')) | v2_struct_0(k6_tmap_1('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_22142, c_78])).
% 12.84/4.78  tff(c_22148, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v2_struct_0('#skF_8') | ~v1_funct_2(k7_tmap_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'), u1_struct_0(k6_tmap_1('#skF_6', '#skF_7'))) | v2_struct_0(k6_tmap_1('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_1297, c_534, c_948, c_84, c_80, c_22145])).
% 12.84/4.78  tff(c_22149, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v1_funct_2(k7_tmap_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'), u1_struct_0(k6_tmap_1('#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_94, c_1058, c_86, c_22148])).
% 12.84/4.78  tff(c_22253, plain, (~v1_funct_2(k7_tmap_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'), u1_struct_0(k6_tmap_1('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_22149])).
% 12.84/4.78  tff(c_22256, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_22253])).
% 12.84/4.78  tff(c_22259, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_22256])).
% 12.84/4.78  tff(c_22261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_22259])).
% 12.84/4.78  tff(c_22262, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~r1_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_22149])).
% 12.84/4.78  tff(c_22400, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_6', '#skF_7'), k7_tmap_1('#skF_6', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_22262])).
% 12.84/4.78  tff(c_22403, plain, (r2_hidden('#skF_9', '#skF_7') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_22400])).
% 12.84/4.78  tff(c_22406, plain, (r2_hidden('#skF_9', '#skF_7') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_22403])).
% 12.84/4.78  tff(c_22407, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_482, c_22406])).
% 12.84/4.78  tff(c_22410, plain, (~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_3368, c_22407])).
% 12.84/4.78  tff(c_22413, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_84, c_22410])).
% 12.84/4.78  tff(c_22415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_22413])).
% 12.84/4.78  tff(c_22416, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_22262])).
% 12.84/4.78  tff(c_22420, plain, (~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_3368, c_22416])).
% 12.84/4.78  tff(c_22423, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_84, c_22420])).
% 12.84/4.78  tff(c_22425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_22423])).
% 12.84/4.78  tff(c_22426, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_290])).
% 12.84/4.78  tff(c_185, plain, (![A_150, B_151]: (~v1_xboole_0(A_150) | r1_tarski(A_150, B_151))), inference(resolution, [status(thm)], [c_163, c_2])).
% 12.84/4.78  tff(c_30, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.84/4.78  tff(c_193, plain, (![B_152, A_153]: (B_152=A_153 | ~r1_tarski(B_152, A_153) | ~v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_185, c_30])).
% 12.84/4.78  tff(c_203, plain, (![B_149, A_148]: (B_149=A_148 | ~v1_xboole_0(B_149) | ~v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_183, c_193])).
% 12.84/4.78  tff(c_22430, plain, (![A_148]: (u1_struct_0('#skF_8')=A_148 | ~v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_22426, c_203])).
% 12.84/4.78  tff(c_22657, plain, (![A_851]: (k4_xboole_0(A_851, A_851)=u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_22647, c_22430])).
% 12.84/4.78  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.84/4.78  tff(c_22753, plain, (![D_857, A_858]: (~r2_hidden(D_857, A_858) | ~r2_hidden(D_857, u1_struct_0('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_22657, c_14])).
% 12.84/4.78  tff(c_22813, plain, (![A_863]: (~r2_hidden('#skF_1'(A_863), u1_struct_0('#skF_8')) | v1_xboole_0(A_863))), inference(resolution, [status(thm)], [c_4, c_22753])).
% 12.84/4.78  tff(c_22837, plain, (![A_864]: (~r1_tarski(A_864, u1_struct_0('#skF_8')) | v1_xboole_0(A_864))), inference(resolution, [status(thm)], [c_266, c_22813])).
% 12.84/4.78  tff(c_22841, plain, (v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_22447, c_22837])).
% 12.84/4.78  tff(c_22852, plain, (v1_xboole_0('#skF_5'('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22543, c_22841])).
% 12.84/4.78  tff(c_22854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_22548, c_22852])).
% 12.84/4.78  tff(c_22855, plain, (v1_xboole_0('#skF_5'('#skF_8'))), inference(splitRight, [status(thm)], [c_22542])).
% 12.84/4.78  tff(c_50, plain, (![A_28]: (~v1_xboole_0('#skF_5'(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.84/4.78  tff(c_22864, plain, (~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_22855, c_50])).
% 12.84/4.78  tff(c_22869, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22543, c_22864])).
% 12.84/4.78  tff(c_22871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_22869])).
% 12.84/4.78  tff(c_22872, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_161])).
% 12.84/4.78  tff(c_22882, plain, (![D_867, A_868, B_869]: (r2_hidden(D_867, A_868) | ~r2_hidden(D_867, k4_xboole_0(A_868, B_869)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.84/4.78  tff(c_23191, plain, (![A_898, B_899]: (r2_hidden('#skF_1'(k4_xboole_0(A_898, B_899)), A_898) | v1_xboole_0(k4_xboole_0(A_898, B_899)))), inference(resolution, [status(thm)], [c_4, c_22882])).
% 12.84/4.78  tff(c_23228, plain, (![A_900, B_901]: (~v1_xboole_0(A_900) | v1_xboole_0(k4_xboole_0(A_900, B_901)))), inference(resolution, [status(thm)], [c_23191, c_2])).
% 12.84/4.78  tff(c_22874, plain, (![A_865, B_866]: (~v1_xboole_0(A_865) | r1_tarski(A_865, B_866))), inference(resolution, [status(thm)], [c_163, c_2])).
% 12.84/4.78  tff(c_22900, plain, (![B_870, A_871]: (B_870=A_871 | ~r1_tarski(B_870, A_871) | ~v1_xboole_0(A_871))), inference(resolution, [status(thm)], [c_22874, c_30])).
% 12.84/4.78  tff(c_22915, plain, (![B_873, A_874]: (B_873=A_874 | ~v1_xboole_0(B_873) | ~v1_xboole_0(A_874))), inference(resolution, [status(thm)], [c_183, c_22900])).
% 12.84/4.78  tff(c_22918, plain, (![A_874]: (u1_struct_0('#skF_8')=A_874 | ~v1_xboole_0(A_874))), inference(resolution, [status(thm)], [c_22872, c_22915])).
% 12.84/4.78  tff(c_23244, plain, (![A_902, B_903]: (k4_xboole_0(A_902, B_903)=u1_struct_0('#skF_8') | ~v1_xboole_0(A_902))), inference(resolution, [status(thm)], [c_23228, c_22918])).
% 12.84/4.78  tff(c_23269, plain, (![B_906]: (k4_xboole_0(u1_struct_0('#skF_8'), B_906)=u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_22872, c_23244])).
% 12.84/4.78  tff(c_23328, plain, (![D_909, B_910]: (~r2_hidden(D_909, B_910) | ~r2_hidden(D_909, u1_struct_0('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_23269, c_14])).
% 12.84/4.78  tff(c_23373, plain, (![A_911]: (~r2_hidden('#skF_1'(A_911), u1_struct_0('#skF_8')) | v1_xboole_0(A_911))), inference(resolution, [status(thm)], [c_4, c_23328])).
% 12.84/4.78  tff(c_23402, plain, (![A_912]: (~r1_tarski(A_912, u1_struct_0('#skF_8')) | v1_xboole_0(A_912))), inference(resolution, [status(thm)], [c_22969, c_23373])).
% 12.84/4.78  tff(c_23406, plain, (v1_xboole_0('#skF_5'('#skF_8')) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_22999, c_23402])).
% 12.84/4.78  tff(c_23417, plain, (v1_xboole_0('#skF_5'('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23127, c_23406])).
% 12.84/4.78  tff(c_23419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_23156, c_23417])).
% 12.84/4.78  tff(c_23420, plain, (v1_xboole_0('#skF_5'('#skF_8'))), inference(splitRight, [status(thm)], [c_23126])).
% 12.84/4.78  tff(c_23429, plain, (~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_23420, c_50])).
% 12.84/4.78  tff(c_23434, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23127, c_23429])).
% 12.84/4.78  tff(c_23436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_23434])).
% 12.84/4.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.84/4.78  
% 12.84/4.78  Inference rules
% 12.84/4.78  ----------------------
% 12.84/4.78  #Ref     : 0
% 12.84/4.78  #Sup     : 5936
% 12.84/4.78  #Fact    : 0
% 12.84/4.78  #Define  : 0
% 12.84/4.78  #Split   : 18
% 12.84/4.78  #Chain   : 0
% 12.84/4.78  #Close   : 0
% 12.84/4.78  
% 12.84/4.78  Ordering : KBO
% 12.84/4.78  
% 12.84/4.78  Simplification rules
% 12.84/4.78  ----------------------
% 12.84/4.78  #Subsume      : 2488
% 12.84/4.78  #Demod        : 2757
% 12.84/4.78  #Tautology    : 1300
% 12.84/4.78  #SimpNegUnit  : 178
% 12.84/4.78  #BackRed      : 34
% 12.84/4.78  
% 12.84/4.78  #Partial instantiations: 0
% 12.84/4.78  #Strategies tried      : 1
% 12.84/4.78  
% 12.84/4.78  Timing (in seconds)
% 12.84/4.78  ----------------------
% 12.84/4.79  Preprocessing        : 0.38
% 12.84/4.79  Parsing              : 0.21
% 12.84/4.79  CNF conversion       : 0.04
% 12.84/4.79  Main loop            : 3.56
% 12.84/4.79  Inferencing          : 0.80
% 12.84/4.79  Reduction            : 1.24
% 12.84/4.79  Demodulation         : 0.92
% 12.84/4.79  BG Simplification    : 0.09
% 12.84/4.79  Subsumption          : 1.17
% 12.84/4.79  Abstraction          : 0.12
% 12.84/4.79  MUC search           : 0.00
% 12.84/4.79  Cooper               : 0.00
% 12.84/4.79  Total                : 4.00
% 12.84/4.79  Index Insertion      : 0.00
% 12.84/4.79  Index Deletion       : 0.00
% 12.84/4.79  Index Matching       : 0.00
% 12.84/4.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
