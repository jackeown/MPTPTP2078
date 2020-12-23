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
% DateTime   : Thu Dec  3 10:27:54 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 575 expanded)
%              Number of leaves         :   48 ( 228 expanded)
%              Depth                    :   15
%              Number of atoms          :  402 (2289 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

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

tff(f_249,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_185,axiom,(
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

tff(f_151,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_167,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_225,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_80,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_72,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_2627,plain,(
    ! [B_447,A_448] :
      ( v2_pre_topc(B_447)
      | ~ m1_pre_topc(B_447,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2630,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2627])).

tff(c_2633,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2630])).

tff(c_96,plain,(
    ! [B_129,A_130] :
      ( l1_pre_topc(B_129)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_96])).

tff(c_102,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_99])).

tff(c_2814,plain,(
    ! [A_469] :
      ( m1_subset_1('#skF_4'(A_469),k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3082,plain,(
    ! [A_500] :
      ( r1_tarski('#skF_4'(A_500),u1_struct_0(A_500))
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_2814,c_26])).

tff(c_217,plain,(
    ! [B_159,A_160] :
      ( v2_pre_topc(B_159)
      | ~ m1_pre_topc(B_159,A_160)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_220,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_217])).

tff(c_223,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_220])).

tff(c_2381,plain,(
    ! [A_425] :
      ( m1_subset_1('#skF_4'(A_425),k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2529,plain,(
    ! [A_445] :
      ( r1_tarski('#skF_4'(A_445),u1_struct_0(A_445))
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(resolution,[status(thm)],[c_2381,c_26])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_912,plain,(
    ! [C_238,A_239,B_240] :
      ( m1_subset_1(C_238,u1_struct_0(A_239))
      | ~ m1_subset_1(C_238,u1_struct_0(B_240))
      | ~ m1_pre_topc(B_240,A_239)
      | v2_struct_0(B_240)
      | ~ l1_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_914,plain,(
    ! [A_239] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_239))
      | ~ m1_pre_topc('#skF_7',A_239)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_68,c_912])).

tff(c_917,plain,(
    ! [A_239] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_239))
      | ~ m1_pre_topc('#skF_7',A_239)
      | ~ l1_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_914])).

tff(c_142,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),A_147)
      | r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [A_147,B_148] :
      ( ~ v1_xboole_0(A_147)
      | r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,(
    ! [C_163,B_164,A_165] :
      ( r2_hidden(C_163,B_164)
      | ~ r2_hidden(C_163,A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_253,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),B_167)
      | ~ r1_tarski(A_166,B_167)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_4,c_237])).

tff(c_70,plain,(
    r1_xboole_0(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_161,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ r1_xboole_0(A_151,B_152)
      | ~ r2_hidden(C_153,B_152)
      | ~ r2_hidden(C_153,A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [C_154] :
      ( ~ r2_hidden(C_154,'#skF_6')
      | ~ r2_hidden(C_154,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_70,c_161])).

tff(c_196,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_267,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_253,c_212])).

tff(c_283,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_288,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_152,c_283])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_193,plain,(
    ! [A_17] :
      ( ~ r2_hidden(A_17,'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_17,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_315,plain,(
    ! [A_176] :
      ( ~ r2_hidden(A_176,'#skF_6')
      | ~ m1_subset_1(A_176,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_193])).

tff(c_319,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_315])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_62,plain,(
    ! [A_42,B_46,C_48] :
      ( r1_tmap_1(A_42,k6_tmap_1(A_42,B_46),k7_tmap_1(A_42,B_46),C_48)
      | r2_hidden(C_48,B_46)
      | ~ m1_subset_1(C_48,u1_struct_0(A_42))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( v1_funct_2(k7_tmap_1(A_38,B_39),u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_512,plain,(
    ! [A_201,B_202] :
      ( ~ v2_struct_0(k6_tmap_1(A_201,B_202))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_522,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_512])).

tff(c_527,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_522])).

tff(c_528,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_527])).

tff(c_638,plain,(
    ! [A_216,B_217] :
      ( v2_pre_topc(k6_tmap_1(A_216,B_217))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_648,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_638])).

tff(c_653,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_648])).

tff(c_654,plain,(
    v2_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_653])).

tff(c_389,plain,(
    ! [A_184,B_185] :
      ( l1_pre_topc(k6_tmap_1(A_184,B_185))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_399,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_389])).

tff(c_404,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_399])).

tff(c_405,plain,(
    l1_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_404])).

tff(c_720,plain,(
    ! [A_219,B_220] :
      ( v1_funct_1(k7_tmap_1(A_219,B_220))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_730,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_720])).

tff(c_735,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_730])).

tff(c_736,plain,(
    v1_funct_1(k7_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_735])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k7_tmap_1(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1440,plain,(
    ! [D_301,C_300,B_298,A_302,F_299] :
      ( r1_tmap_1(D_301,A_302,k2_tmap_1(B_298,A_302,C_300,D_301),F_299)
      | ~ r1_tmap_1(B_298,A_302,C_300,F_299)
      | ~ m1_subset_1(F_299,u1_struct_0(D_301))
      | ~ m1_subset_1(F_299,u1_struct_0(B_298))
      | ~ m1_pre_topc(D_301,B_298)
      | v2_struct_0(D_301)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_298),u1_struct_0(A_302))))
      | ~ v1_funct_2(C_300,u1_struct_0(B_298),u1_struct_0(A_302))
      | ~ v1_funct_1(C_300)
      | ~ l1_pre_topc(B_298)
      | ~ v2_pre_topc(B_298)
      | v2_struct_0(B_298)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_2235,plain,(
    ! [D_407,A_408,B_409,F_410] :
      ( r1_tmap_1(D_407,k6_tmap_1(A_408,B_409),k2_tmap_1(A_408,k6_tmap_1(A_408,B_409),k7_tmap_1(A_408,B_409),D_407),F_410)
      | ~ r1_tmap_1(A_408,k6_tmap_1(A_408,B_409),k7_tmap_1(A_408,B_409),F_410)
      | ~ m1_subset_1(F_410,u1_struct_0(D_407))
      | ~ m1_subset_1(F_410,u1_struct_0(A_408))
      | ~ m1_pre_topc(D_407,A_408)
      | v2_struct_0(D_407)
      | ~ v1_funct_2(k7_tmap_1(A_408,B_409),u1_struct_0(A_408),u1_struct_0(k6_tmap_1(A_408,B_409)))
      | ~ v1_funct_1(k7_tmap_1(A_408,B_409))
      | ~ l1_pre_topc(k6_tmap_1(A_408,B_409))
      | ~ v2_pre_topc(k6_tmap_1(A_408,B_409))
      | v2_struct_0(k6_tmap_1(A_408,B_409))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_50,c_1440])).

tff(c_66,plain,(
    ~ r1_tmap_1('#skF_7',k6_tmap_1('#skF_5','#skF_6'),k2_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_2238,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_7')
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6')))
    | ~ v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2235,c_66])).

tff(c_2241,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_7')
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6')))
    | v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_654,c_405,c_736,c_72,c_68,c_2238])).

tff(c_2242,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_528,c_74,c_2241])).

tff(c_2248,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2242])).

tff(c_2251,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2248])).

tff(c_2254,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_2251])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2254])).

tff(c_2257,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2242])).

tff(c_2266,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2257])).

tff(c_2269,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2266])).

tff(c_2272,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_2269])).

tff(c_2273,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_319,c_2272])).

tff(c_2276,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_917,c_2273])).

tff(c_2279,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_2276])).

tff(c_2281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2279])).

tff(c_2282,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2257])).

tff(c_2286,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_917,c_2282])).

tff(c_2289,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_2286])).

tff(c_2291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2289])).

tff(c_2293,plain,(
    r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2428,plain,(
    ! [A_435,B_436,B_437] :
      ( r2_hidden('#skF_2'(A_435,B_436),B_437)
      | ~ r1_tarski(A_435,B_437)
      | r1_tarski(A_435,B_436) ) ),
    inference(resolution,[status(thm)],[c_10,c_237])).

tff(c_192,plain,(
    ! [B_6] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_6),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_7'),B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_2432,plain,(
    ! [B_436] :
      ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_7'),B_436) ) ),
    inference(resolution,[status(thm)],[c_2428,c_192])).

tff(c_2456,plain,(
    ! [B_438] : r1_tarski(u1_struct_0('#skF_7'),B_438) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_2432])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2479,plain,(
    ! [B_438] :
      ( u1_struct_0('#skF_7') = B_438
      | ~ r1_tarski(B_438,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2456,c_18])).

tff(c_2535,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2529,c_2479])).

tff(c_2553,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_102,c_2535])).

tff(c_2554,plain,(
    u1_struct_0('#skF_7') = '#skF_4'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2553])).

tff(c_2292,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_2573,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2554,c_2292])).

tff(c_40,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0('#skF_4'(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2604,plain,
    ( ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2573,c_40])).

tff(c_2609,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_102,c_2604])).

tff(c_2611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2609])).

tff(c_2612,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_2635,plain,(
    ! [C_450,B_451,A_452] :
      ( r2_hidden(C_450,B_451)
      | ~ r2_hidden(C_450,A_452)
      | ~ r1_tarski(A_452,B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2930,plain,(
    ! [A_486,B_487,B_488] :
      ( r2_hidden('#skF_2'(A_486,B_487),B_488)
      | ~ r1_tarski(A_486,B_488)
      | r1_tarski(A_486,B_487) ) ),
    inference(resolution,[status(thm)],[c_10,c_2635])).

tff(c_2948,plain,(
    ! [B_487] :
      ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_7'),B_487) ) ),
    inference(resolution,[status(thm)],[c_2930,c_192])).

tff(c_2963,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2948])).

tff(c_2966,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_152,c_2963])).

tff(c_2970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2612,c_2966])).

tff(c_2975,plain,(
    ! [B_492] : r1_tarski(u1_struct_0('#skF_7'),B_492) ),
    inference(splitRight,[status(thm)],[c_2948])).

tff(c_3011,plain,(
    ! [B_492] :
      ( u1_struct_0('#skF_7') = B_492
      | ~ r1_tarski(B_492,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2975,c_18])).

tff(c_3089,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3082,c_3011])).

tff(c_3118,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2633,c_102,c_3089])).

tff(c_3119,plain,(
    u1_struct_0('#skF_7') = '#skF_4'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3118])).

tff(c_3154,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_2612])).

tff(c_3188,plain,
    ( ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3154,c_40])).

tff(c_3193,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2633,c_102,c_3188])).

tff(c_3195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.28/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.04  
% 5.50/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.04  %$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 5.50/2.04  
% 5.50/2.04  %Foreground sorts:
% 5.50/2.04  
% 5.50/2.04  
% 5.50/2.04  %Background operators:
% 5.50/2.04  
% 5.50/2.04  
% 5.50/2.04  %Foreground operators:
% 5.50/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.50/2.04  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 5.50/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.50/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.50/2.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.50/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.50/2.04  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.50/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.50/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.50/2.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.50/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.50/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.50/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.50/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.50/2.04  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.50/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.50/2.04  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.50/2.04  tff('#skF_8', type, '#skF_8': $i).
% 5.50/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.50/2.04  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.50/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.50/2.04  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.50/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.50/2.04  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.50/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.50/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.50/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.50/2.04  
% 5.58/2.07  tff(f_249, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 5.58/2.07  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.58/2.07  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.58/2.07  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 5.58/2.07  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.58/2.07  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.58/2.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.58/2.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.58/2.07  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.58/2.07  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.58/2.07  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 5.58/2.07  tff(f_151, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 5.58/2.07  tff(f_167, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 5.58/2.07  tff(f_136, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 5.58/2.07  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.58/2.07  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.58/2.07  tff(c_74, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_80, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_78, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_72, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_2627, plain, (![B_447, A_448]: (v2_pre_topc(B_447) | ~m1_pre_topc(B_447, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.58/2.07  tff(c_2630, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2627])).
% 5.58/2.07  tff(c_2633, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2630])).
% 5.58/2.07  tff(c_96, plain, (![B_129, A_130]: (l1_pre_topc(B_129) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.58/2.07  tff(c_99, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_96])).
% 5.58/2.07  tff(c_102, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_99])).
% 5.58/2.07  tff(c_2814, plain, (![A_469]: (m1_subset_1('#skF_4'(A_469), k1_zfmisc_1(u1_struct_0(A_469))) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.58/2.07  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.58/2.07  tff(c_3082, plain, (![A_500]: (r1_tarski('#skF_4'(A_500), u1_struct_0(A_500)) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_2814, c_26])).
% 5.58/2.07  tff(c_217, plain, (![B_159, A_160]: (v2_pre_topc(B_159) | ~m1_pre_topc(B_159, A_160) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.58/2.07  tff(c_220, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_217])).
% 5.58/2.07  tff(c_223, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_220])).
% 5.58/2.07  tff(c_2381, plain, (![A_425]: (m1_subset_1('#skF_4'(A_425), k1_zfmisc_1(u1_struct_0(A_425))) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.58/2.07  tff(c_2529, plain, (![A_445]: (r1_tarski('#skF_4'(A_445), u1_struct_0(A_445)) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(resolution, [status(thm)], [c_2381, c_26])).
% 5.58/2.07  tff(c_82, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_68, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_912, plain, (![C_238, A_239, B_240]: (m1_subset_1(C_238, u1_struct_0(A_239)) | ~m1_subset_1(C_238, u1_struct_0(B_240)) | ~m1_pre_topc(B_240, A_239) | v2_struct_0(B_240) | ~l1_pre_topc(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.58/2.07  tff(c_914, plain, (![A_239]: (m1_subset_1('#skF_8', u1_struct_0(A_239)) | ~m1_pre_topc('#skF_7', A_239) | v2_struct_0('#skF_7') | ~l1_pre_topc(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_68, c_912])).
% 5.58/2.07  tff(c_917, plain, (![A_239]: (m1_subset_1('#skF_8', u1_struct_0(A_239)) | ~m1_pre_topc('#skF_7', A_239) | ~l1_pre_topc(A_239) | v2_struct_0(A_239))), inference(negUnitSimplification, [status(thm)], [c_74, c_914])).
% 5.58/2.07  tff(c_142, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), A_147) | r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.58/2.07  tff(c_152, plain, (![A_147, B_148]: (~v1_xboole_0(A_147) | r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_142, c_2])).
% 5.58/2.07  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.58/2.07  tff(c_237, plain, (![C_163, B_164, A_165]: (r2_hidden(C_163, B_164) | ~r2_hidden(C_163, A_165) | ~r1_tarski(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.07  tff(c_253, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), B_167) | ~r1_tarski(A_166, B_167) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_4, c_237])).
% 5.58/2.07  tff(c_70, plain, (r1_xboole_0(u1_struct_0('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_161, plain, (![A_151, B_152, C_153]: (~r1_xboole_0(A_151, B_152) | ~r2_hidden(C_153, B_152) | ~r2_hidden(C_153, A_151))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.58/2.07  tff(c_171, plain, (![C_154]: (~r2_hidden(C_154, '#skF_6') | ~r2_hidden(C_154, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_70, c_161])).
% 5.58/2.07  tff(c_196, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_171])).
% 5.58/2.07  tff(c_212, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6')), inference(splitLeft, [status(thm)], [c_196])).
% 5.58/2.07  tff(c_267, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_253, c_212])).
% 5.58/2.07  tff(c_283, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_267])).
% 5.58/2.07  tff(c_288, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_152, c_283])).
% 5.58/2.07  tff(c_24, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.58/2.07  tff(c_193, plain, (![A_17]: (~r2_hidden(A_17, '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1(A_17, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_171])).
% 5.58/2.07  tff(c_315, plain, (![A_176]: (~r2_hidden(A_176, '#skF_6') | ~m1_subset_1(A_176, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_288, c_193])).
% 5.58/2.07  tff(c_319, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_315])).
% 5.58/2.07  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_62, plain, (![A_42, B_46, C_48]: (r1_tmap_1(A_42, k6_tmap_1(A_42, B_46), k7_tmap_1(A_42, B_46), C_48) | r2_hidden(C_48, B_46) | ~m1_subset_1(C_48, u1_struct_0(A_42)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_185])).
% 5.58/2.07  tff(c_52, plain, (![A_38, B_39]: (v1_funct_2(k7_tmap_1(A_38, B_39), u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.58/2.07  tff(c_512, plain, (![A_201, B_202]: (~v2_struct_0(k6_tmap_1(A_201, B_202)) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.58/2.07  tff(c_522, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_512])).
% 5.58/2.07  tff(c_527, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_522])).
% 5.58/2.07  tff(c_528, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_527])).
% 5.58/2.07  tff(c_638, plain, (![A_216, B_217]: (v2_pre_topc(k6_tmap_1(A_216, B_217)) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.58/2.07  tff(c_648, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_638])).
% 5.58/2.07  tff(c_653, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_648])).
% 5.58/2.07  tff(c_654, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_653])).
% 5.58/2.07  tff(c_389, plain, (![A_184, B_185]: (l1_pre_topc(k6_tmap_1(A_184, B_185)) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.58/2.07  tff(c_399, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_389])).
% 5.58/2.07  tff(c_404, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_399])).
% 5.58/2.07  tff(c_405, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_404])).
% 5.58/2.07  tff(c_720, plain, (![A_219, B_220]: (v1_funct_1(k7_tmap_1(A_219, B_220)) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.58/2.07  tff(c_730, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_720])).
% 5.58/2.07  tff(c_735, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_730])).
% 5.58/2.07  tff(c_736, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_735])).
% 5.58/2.07  tff(c_50, plain, (![A_38, B_39]: (m1_subset_1(k7_tmap_1(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.58/2.07  tff(c_1440, plain, (![D_301, C_300, B_298, A_302, F_299]: (r1_tmap_1(D_301, A_302, k2_tmap_1(B_298, A_302, C_300, D_301), F_299) | ~r1_tmap_1(B_298, A_302, C_300, F_299) | ~m1_subset_1(F_299, u1_struct_0(D_301)) | ~m1_subset_1(F_299, u1_struct_0(B_298)) | ~m1_pre_topc(D_301, B_298) | v2_struct_0(D_301) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_298), u1_struct_0(A_302)))) | ~v1_funct_2(C_300, u1_struct_0(B_298), u1_struct_0(A_302)) | ~v1_funct_1(C_300) | ~l1_pre_topc(B_298) | ~v2_pre_topc(B_298) | v2_struct_0(B_298) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_225])).
% 5.58/2.07  tff(c_2235, plain, (![D_407, A_408, B_409, F_410]: (r1_tmap_1(D_407, k6_tmap_1(A_408, B_409), k2_tmap_1(A_408, k6_tmap_1(A_408, B_409), k7_tmap_1(A_408, B_409), D_407), F_410) | ~r1_tmap_1(A_408, k6_tmap_1(A_408, B_409), k7_tmap_1(A_408, B_409), F_410) | ~m1_subset_1(F_410, u1_struct_0(D_407)) | ~m1_subset_1(F_410, u1_struct_0(A_408)) | ~m1_pre_topc(D_407, A_408) | v2_struct_0(D_407) | ~v1_funct_2(k7_tmap_1(A_408, B_409), u1_struct_0(A_408), u1_struct_0(k6_tmap_1(A_408, B_409))) | ~v1_funct_1(k7_tmap_1(A_408, B_409)) | ~l1_pre_topc(k6_tmap_1(A_408, B_409)) | ~v2_pre_topc(k6_tmap_1(A_408, B_409)) | v2_struct_0(k6_tmap_1(A_408, B_409)) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_50, c_1440])).
% 5.58/2.07  tff(c_66, plain, (~r1_tmap_1('#skF_7', k6_tmap_1('#skF_5', '#skF_6'), k2_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.58/2.07  tff(c_2238, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2235, c_66])).
% 5.58/2.07  tff(c_2241, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_654, c_405, c_736, c_72, c_68, c_2238])).
% 5.58/2.07  tff(c_2242, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_82, c_528, c_74, c_2241])).
% 5.58/2.07  tff(c_2248, plain, (~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_2242])).
% 5.58/2.07  tff(c_2251, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_2248])).
% 5.58/2.07  tff(c_2254, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_2251])).
% 5.58/2.07  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2254])).
% 5.58/2.07  tff(c_2257, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_2242])).
% 5.58/2.07  tff(c_2266, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_2257])).
% 5.58/2.07  tff(c_2269, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2266])).
% 5.58/2.07  tff(c_2272, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_2269])).
% 5.58/2.07  tff(c_2273, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_319, c_2272])).
% 5.58/2.07  tff(c_2276, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_917, c_2273])).
% 5.58/2.07  tff(c_2279, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_2276])).
% 5.58/2.07  tff(c_2281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2279])).
% 5.58/2.07  tff(c_2282, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2257])).
% 5.58/2.07  tff(c_2286, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_917, c_2282])).
% 5.58/2.07  tff(c_2289, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_2286])).
% 5.58/2.07  tff(c_2291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2289])).
% 5.58/2.07  tff(c_2293, plain, (r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_267])).
% 5.58/2.07  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.07  tff(c_2428, plain, (![A_435, B_436, B_437]: (r2_hidden('#skF_2'(A_435, B_436), B_437) | ~r1_tarski(A_435, B_437) | r1_tarski(A_435, B_436))), inference(resolution, [status(thm)], [c_10, c_237])).
% 5.58/2.07  tff(c_192, plain, (![B_6]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_6), '#skF_6') | r1_tarski(u1_struct_0('#skF_7'), B_6))), inference(resolution, [status(thm)], [c_10, c_171])).
% 5.58/2.07  tff(c_2432, plain, (![B_436]: (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | r1_tarski(u1_struct_0('#skF_7'), B_436))), inference(resolution, [status(thm)], [c_2428, c_192])).
% 5.58/2.07  tff(c_2456, plain, (![B_438]: (r1_tarski(u1_struct_0('#skF_7'), B_438))), inference(demodulation, [status(thm), theory('equality')], [c_2293, c_2432])).
% 5.58/2.07  tff(c_18, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.58/2.07  tff(c_2479, plain, (![B_438]: (u1_struct_0('#skF_7')=B_438 | ~r1_tarski(B_438, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_2456, c_18])).
% 5.58/2.07  tff(c_2535, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2529, c_2479])).
% 5.58/2.07  tff(c_2553, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_102, c_2535])).
% 5.58/2.07  tff(c_2554, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_2553])).
% 5.58/2.07  tff(c_2292, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_267])).
% 5.58/2.07  tff(c_2573, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2554, c_2292])).
% 5.58/2.07  tff(c_40, plain, (![A_34]: (~v1_xboole_0('#skF_4'(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.58/2.07  tff(c_2604, plain, (~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2573, c_40])).
% 5.58/2.07  tff(c_2609, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_102, c_2604])).
% 5.58/2.07  tff(c_2611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2609])).
% 5.58/2.07  tff(c_2612, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_196])).
% 5.58/2.07  tff(c_2635, plain, (![C_450, B_451, A_452]: (r2_hidden(C_450, B_451) | ~r2_hidden(C_450, A_452) | ~r1_tarski(A_452, B_451))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.07  tff(c_2930, plain, (![A_486, B_487, B_488]: (r2_hidden('#skF_2'(A_486, B_487), B_488) | ~r1_tarski(A_486, B_488) | r1_tarski(A_486, B_487))), inference(resolution, [status(thm)], [c_10, c_2635])).
% 5.58/2.07  tff(c_2948, plain, (![B_487]: (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | r1_tarski(u1_struct_0('#skF_7'), B_487))), inference(resolution, [status(thm)], [c_2930, c_192])).
% 5.58/2.07  tff(c_2963, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2948])).
% 5.58/2.07  tff(c_2966, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_152, c_2963])).
% 5.58/2.07  tff(c_2970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2612, c_2966])).
% 5.58/2.07  tff(c_2975, plain, (![B_492]: (r1_tarski(u1_struct_0('#skF_7'), B_492))), inference(splitRight, [status(thm)], [c_2948])).
% 5.58/2.07  tff(c_3011, plain, (![B_492]: (u1_struct_0('#skF_7')=B_492 | ~r1_tarski(B_492, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_2975, c_18])).
% 5.58/2.07  tff(c_3089, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3082, c_3011])).
% 5.58/2.07  tff(c_3118, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2633, c_102, c_3089])).
% 5.58/2.07  tff(c_3119, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_3118])).
% 5.58/2.07  tff(c_3154, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_2612])).
% 5.58/2.07  tff(c_3188, plain, (~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3154, c_40])).
% 5.58/2.07  tff(c_3193, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2633, c_102, c_3188])).
% 5.58/2.07  tff(c_3195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3193])).
% 5.58/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.07  
% 5.58/2.07  Inference rules
% 5.58/2.07  ----------------------
% 5.58/2.07  #Ref     : 0
% 5.58/2.07  #Sup     : 612
% 5.58/2.07  #Fact    : 0
% 5.58/2.07  #Define  : 0
% 5.58/2.07  #Split   : 20
% 5.58/2.07  #Chain   : 0
% 5.58/2.07  #Close   : 0
% 5.58/2.07  
% 5.58/2.07  Ordering : KBO
% 5.58/2.07  
% 5.58/2.07  Simplification rules
% 5.58/2.07  ----------------------
% 5.58/2.07  #Subsume      : 208
% 5.58/2.07  #Demod        : 218
% 5.58/2.07  #Tautology    : 76
% 5.58/2.07  #SimpNegUnit  : 118
% 5.58/2.07  #BackRed      : 41
% 5.58/2.07  
% 5.58/2.07  #Partial instantiations: 0
% 5.58/2.07  #Strategies tried      : 1
% 5.58/2.07  
% 5.58/2.07  Timing (in seconds)
% 5.58/2.07  ----------------------
% 5.58/2.07  Preprocessing        : 0.37
% 5.58/2.07  Parsing              : 0.21
% 5.58/2.07  CNF conversion       : 0.03
% 5.58/2.07  Main loop            : 0.87
% 5.58/2.07  Inferencing          : 0.30
% 5.58/2.07  Reduction            : 0.25
% 5.58/2.07  Demodulation         : 0.15
% 5.58/2.07  BG Simplification    : 0.03
% 5.58/2.07  Subsumption          : 0.23
% 5.58/2.07  Abstraction          : 0.03
% 5.58/2.07  MUC search           : 0.00
% 5.58/2.07  Cooper               : 0.00
% 5.58/2.07  Total                : 1.29
% 5.58/2.07  Index Insertion      : 0.00
% 5.58/2.07  Index Deletion       : 0.00
% 5.58/2.07  Index Matching       : 0.00
% 5.58/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
