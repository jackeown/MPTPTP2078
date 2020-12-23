%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:54 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 454 expanded)
%              Number of leaves         :   46 ( 187 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (1900 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v2_compts_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_247,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v2_compts_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_compts_1)).

tff(f_72,axiom,(
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

tff(f_183,axiom,(
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

tff(f_149,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_223,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_78,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_70,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_175,plain,(
    ! [B_156,A_157] :
      ( v2_pre_topc(B_156)
      | ~ m1_pre_topc(B_156,A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_175])).

tff(c_181,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_178])).

tff(c_94,plain,(
    ! [B_129,A_130] :
      ( l1_pre_topc(B_129)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_2584,plain,(
    ! [A_443] :
      ( m1_subset_1('#skF_4'(A_443),k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3064,plain,(
    ! [A_500] :
      ( r1_tarski('#skF_4'(A_500),u1_struct_0(A_500))
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_2584,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [C_161,B_162,A_163] :
      ( r2_hidden(C_161,B_162)
      | ~ r2_hidden(C_161,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_207,plain,(
    ! [A_1,B_162] :
      ( r2_hidden('#skF_1'(A_1),B_162)
      | ~ r1_tarski(A_1,B_162)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_988,plain,(
    ! [C_237,A_238,B_239] :
      ( m1_subset_1(C_237,u1_struct_0(A_238))
      | ~ m1_subset_1(C_237,u1_struct_0(B_239))
      | ~ m1_pre_topc(B_239,A_238)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_990,plain,(
    ! [A_238] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_238))
      | ~ m1_pre_topc('#skF_7',A_238)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_66,c_988])).

tff(c_993,plain,(
    ! [A_238] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_238))
      | ~ m1_pre_topc('#skF_7',A_238)
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_990])).

tff(c_140,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),A_147)
      | r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_147,B_148] :
      ( ~ v1_xboole_0(A_147)
      | r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_245,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166),B_167)
      | ~ r1_tarski(A_166,B_167)
      | v1_xboole_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_68,plain,(
    r1_xboole_0(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_182,plain,(
    ! [A_158,B_159,C_160] :
      ( ~ r1_xboole_0(A_158,B_159)
      | ~ r2_hidden(C_160,B_159)
      | ~ r2_hidden(C_160,A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_208,plain,(
    ! [C_164] :
      ( ~ r2_hidden(C_164,'#skF_6')
      | ~ r2_hidden(C_164,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_68,c_182])).

tff(c_233,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_258,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_245,c_234])).

tff(c_275,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_280,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_150,c_275])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_230,plain,(
    ! [A_17] :
      ( ~ r2_hidden(A_17,'#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ m1_subset_1(A_17,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_208])).

tff(c_351,plain,(
    ! [A_178] :
      ( ~ r2_hidden(A_178,'#skF_6')
      | ~ m1_subset_1(A_178,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_230])).

tff(c_355,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_351])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_60,plain,(
    ! [A_42,B_46,C_48] :
      ( r1_tmap_1(A_42,k6_tmap_1(A_42,B_46),k7_tmap_1(A_42,B_46),C_48)
      | r2_hidden(C_48,B_46)
      | ~ m1_subset_1(C_48,u1_struct_0(A_42))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( v1_funct_2(k7_tmap_1(A_38,B_39),u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_660,plain,(
    ! [A_205,B_206] :
      ( ~ v2_struct_0(k6_tmap_1(A_205,B_206))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_670,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_660])).

tff(c_675,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_670])).

tff(c_676,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_675])).

tff(c_761,plain,(
    ! [A_213,B_214] :
      ( v2_pre_topc(k6_tmap_1(A_213,B_214))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_771,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_761])).

tff(c_776,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_771])).

tff(c_777,plain,(
    v2_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_776])).

tff(c_528,plain,(
    ! [A_191,B_192] :
      ( l1_pre_topc(k6_tmap_1(A_191,B_192))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_538,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_528])).

tff(c_543,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_538])).

tff(c_544,plain,(
    l1_pre_topc(k6_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_543])).

tff(c_388,plain,(
    ! [A_181,B_182] :
      ( v1_funct_1(k7_tmap_1(A_181,B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_398,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_388])).

tff(c_403,plain,
    ( v1_funct_1(k7_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_398])).

tff(c_404,plain,(
    v1_funct_1(k7_tmap_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_403])).

tff(c_48,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k7_tmap_1(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(k6_tmap_1(A_38,B_39)))))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1472,plain,(
    ! [B_306,D_309,C_308,A_310,F_307] :
      ( r1_tmap_1(D_309,A_310,k2_tmap_1(B_306,A_310,C_308,D_309),F_307)
      | ~ r1_tmap_1(B_306,A_310,C_308,F_307)
      | ~ m1_subset_1(F_307,u1_struct_0(D_309))
      | ~ m1_subset_1(F_307,u1_struct_0(B_306))
      | ~ m1_pre_topc(D_309,B_306)
      | v2_struct_0(D_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_306),u1_struct_0(A_310))))
      | ~ v1_funct_2(C_308,u1_struct_0(B_306),u1_struct_0(A_310))
      | ~ v1_funct_1(C_308)
      | ~ l1_pre_topc(B_306)
      | ~ v2_pre_topc(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_2329,plain,(
    ! [D_417,A_418,B_419,F_420] :
      ( r1_tmap_1(D_417,k6_tmap_1(A_418,B_419),k2_tmap_1(A_418,k6_tmap_1(A_418,B_419),k7_tmap_1(A_418,B_419),D_417),F_420)
      | ~ r1_tmap_1(A_418,k6_tmap_1(A_418,B_419),k7_tmap_1(A_418,B_419),F_420)
      | ~ m1_subset_1(F_420,u1_struct_0(D_417))
      | ~ m1_subset_1(F_420,u1_struct_0(A_418))
      | ~ m1_pre_topc(D_417,A_418)
      | v2_struct_0(D_417)
      | ~ v1_funct_2(k7_tmap_1(A_418,B_419),u1_struct_0(A_418),u1_struct_0(k6_tmap_1(A_418,B_419)))
      | ~ v1_funct_1(k7_tmap_1(A_418,B_419))
      | ~ l1_pre_topc(k6_tmap_1(A_418,B_419))
      | ~ v2_pre_topc(k6_tmap_1(A_418,B_419))
      | v2_struct_0(k6_tmap_1(A_418,B_419))
      | ~ m1_subset_1(B_419,k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(resolution,[status(thm)],[c_48,c_1472])).

tff(c_64,plain,(
    ~ r1_tmap_1('#skF_7',k6_tmap_1('#skF_5','#skF_6'),k2_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_2332,plain,
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
    inference(resolution,[status(thm)],[c_2329,c_64])).

tff(c_2335,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_7')
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6')))
    | v2_struct_0(k6_tmap_1('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_777,c_544,c_404,c_70,c_66,c_2332])).

tff(c_2336,plain,
    ( ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_676,c_72,c_2335])).

tff(c_2408,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2336])).

tff(c_2411,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2408])).

tff(c_2414,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2411])).

tff(c_2416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2414])).

tff(c_2417,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2336])).

tff(c_2432,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2417])).

tff(c_2435,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2432])).

tff(c_2438,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2435])).

tff(c_2439,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_355,c_2438])).

tff(c_2461,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_993,c_2439])).

tff(c_2464,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_2461])).

tff(c_2466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2464])).

tff(c_2467,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2417])).

tff(c_2471,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_993,c_2467])).

tff(c_2474,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_2471])).

tff(c_2476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2474])).

tff(c_2478,plain,(
    r1_tarski(u1_struct_0('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2589,plain,(
    ! [A_444,B_445,B_446] :
      ( r2_hidden('#skF_3'(A_444,B_445),B_446)
      | ~ r1_tarski(A_444,B_446)
      | r1_xboole_0(A_444,B_445) ) ),
    inference(resolution,[status(thm)],[c_16,c_192])).

tff(c_232,plain,(
    ! [B_11] :
      ( ~ r2_hidden('#skF_3'(u1_struct_0('#skF_7'),B_11),'#skF_6')
      | r1_xboole_0(u1_struct_0('#skF_7'),B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_208])).

tff(c_2593,plain,(
    ! [B_445] :
      ( ~ r1_tarski(u1_struct_0('#skF_7'),'#skF_6')
      | r1_xboole_0(u1_struct_0('#skF_7'),B_445) ) ),
    inference(resolution,[status(thm)],[c_2589,c_232])).

tff(c_2617,plain,(
    ! [B_447] : r1_xboole_0(u1_struct_0('#skF_7'),B_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_2593])).

tff(c_12,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,B_11)
      | ~ r2_hidden(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2659,plain,(
    ! [C_452,B_453] :
      ( ~ r2_hidden(C_452,B_453)
      | ~ r2_hidden(C_452,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2617,c_12])).

tff(c_2681,plain,(
    ! [A_454] :
      ( ~ r2_hidden('#skF_1'(A_454),u1_struct_0('#skF_7'))
      | v1_xboole_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_4,c_2659])).

tff(c_2693,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,u1_struct_0('#skF_7'))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_207,c_2681])).

tff(c_3084,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3064,c_2693])).

tff(c_3110,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_100,c_3084])).

tff(c_3111,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3110])).

tff(c_38,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0('#skF_4'(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3122,plain,
    ( ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3111,c_38])).

tff(c_3127,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_100,c_3122])).

tff(c_3129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:46:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.00  
% 5.30/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.00  %$ r1_tmap_1 > v1_funct_2 > v2_compts_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 5.30/2.00  
% 5.30/2.00  %Foreground sorts:
% 5.30/2.00  
% 5.30/2.00  
% 5.30/2.00  %Background operators:
% 5.30/2.00  
% 5.30/2.00  
% 5.30/2.00  %Foreground operators:
% 5.30/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.30/2.00  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 5.30/2.00  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 5.30/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.30/2.00  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.30/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.30/2.00  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.30/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.30/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.30/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.30/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.30/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.30/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.30/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.30/2.00  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.30/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.30/2.00  tff('#skF_8', type, '#skF_8': $i).
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.30/2.00  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.30/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.30/2.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.30/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.30/2.00  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.30/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.30/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.30/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.30/2.00  
% 5.30/2.03  tff(f_247, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 5.30/2.03  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.30/2.03  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.30/2.03  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v2_compts_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_compts_1)).
% 5.30/2.03  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.30/2.03  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.30/2.03  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.30/2.03  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.30/2.03  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.30/2.03  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.30/2.03  tff(f_183, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 5.30/2.03  tff(f_149, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 5.30/2.03  tff(f_165, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 5.30/2.03  tff(f_134, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 5.30/2.03  tff(f_223, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.30/2.03  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_78, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_70, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_175, plain, (![B_156, A_157]: (v2_pre_topc(B_156) | ~m1_pre_topc(B_156, A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.30/2.03  tff(c_178, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_175])).
% 5.30/2.03  tff(c_181, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_178])).
% 5.30/2.03  tff(c_94, plain, (![B_129, A_130]: (l1_pre_topc(B_129) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.30/2.03  tff(c_97, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_94])).
% 5.30/2.03  tff(c_100, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_97])).
% 5.30/2.03  tff(c_2584, plain, (![A_443]: (m1_subset_1('#skF_4'(A_443), k1_zfmisc_1(u1_struct_0(A_443))) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.30/2.03  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.30/2.03  tff(c_3064, plain, (![A_500]: (r1_tarski('#skF_4'(A_500), u1_struct_0(A_500)) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_2584, c_26])).
% 5.30/2.03  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.03  tff(c_192, plain, (![C_161, B_162, A_163]: (r2_hidden(C_161, B_162) | ~r2_hidden(C_161, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/2.03  tff(c_207, plain, (![A_1, B_162]: (r2_hidden('#skF_1'(A_1), B_162) | ~r1_tarski(A_1, B_162) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_192])).
% 5.30/2.03  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_988, plain, (![C_237, A_238, B_239]: (m1_subset_1(C_237, u1_struct_0(A_238)) | ~m1_subset_1(C_237, u1_struct_0(B_239)) | ~m1_pre_topc(B_239, A_238) | v2_struct_0(B_239) | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.30/2.03  tff(c_990, plain, (![A_238]: (m1_subset_1('#skF_8', u1_struct_0(A_238)) | ~m1_pre_topc('#skF_7', A_238) | v2_struct_0('#skF_7') | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_66, c_988])).
% 5.30/2.03  tff(c_993, plain, (![A_238]: (m1_subset_1('#skF_8', u1_struct_0(A_238)) | ~m1_pre_topc('#skF_7', A_238) | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(negUnitSimplification, [status(thm)], [c_72, c_990])).
% 5.30/2.03  tff(c_140, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), A_147) | r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/2.03  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.03  tff(c_150, plain, (![A_147, B_148]: (~v1_xboole_0(A_147) | r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_140, c_2])).
% 5.30/2.03  tff(c_245, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166), B_167) | ~r1_tarski(A_166, B_167) | v1_xboole_0(A_166))), inference(resolution, [status(thm)], [c_4, c_192])).
% 5.30/2.03  tff(c_68, plain, (r1_xboole_0(u1_struct_0('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_182, plain, (![A_158, B_159, C_160]: (~r1_xboole_0(A_158, B_159) | ~r2_hidden(C_160, B_159) | ~r2_hidden(C_160, A_158))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.30/2.03  tff(c_208, plain, (![C_164]: (~r2_hidden(C_164, '#skF_6') | ~r2_hidden(C_164, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_68, c_182])).
% 5.30/2.03  tff(c_233, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_208])).
% 5.30/2.03  tff(c_234, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_7')), '#skF_6')), inference(splitLeft, [status(thm)], [c_233])).
% 5.30/2.03  tff(c_258, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_245, c_234])).
% 5.30/2.03  tff(c_275, plain, (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_258])).
% 5.30/2.03  tff(c_280, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_150, c_275])).
% 5.30/2.03  tff(c_24, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.30/2.03  tff(c_230, plain, (![A_17]: (~r2_hidden(A_17, '#skF_6') | v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1(A_17, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_208])).
% 5.30/2.03  tff(c_351, plain, (![A_178]: (~r2_hidden(A_178, '#skF_6') | ~m1_subset_1(A_178, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_280, c_230])).
% 5.30/2.03  tff(c_355, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_351])).
% 5.30/2.03  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_60, plain, (![A_42, B_46, C_48]: (r1_tmap_1(A_42, k6_tmap_1(A_42, B_46), k7_tmap_1(A_42, B_46), C_48) | r2_hidden(C_48, B_46) | ~m1_subset_1(C_48, u1_struct_0(A_42)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.30/2.03  tff(c_50, plain, (![A_38, B_39]: (v1_funct_2(k7_tmap_1(A_38, B_39), u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.30/2.03  tff(c_660, plain, (![A_205, B_206]: (~v2_struct_0(k6_tmap_1(A_205, B_206)) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.30/2.03  tff(c_670, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_660])).
% 5.30/2.03  tff(c_675, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_670])).
% 5.30/2.03  tff(c_676, plain, (~v2_struct_0(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_675])).
% 5.30/2.03  tff(c_761, plain, (![A_213, B_214]: (v2_pre_topc(k6_tmap_1(A_213, B_214)) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.30/2.03  tff(c_771, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_761])).
% 5.30/2.03  tff(c_776, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_771])).
% 5.30/2.03  tff(c_777, plain, (v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_776])).
% 5.30/2.03  tff(c_528, plain, (![A_191, B_192]: (l1_pre_topc(k6_tmap_1(A_191, B_192)) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.30/2.03  tff(c_538, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_528])).
% 5.30/2.03  tff(c_543, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_538])).
% 5.30/2.03  tff(c_544, plain, (l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_543])).
% 5.30/2.03  tff(c_388, plain, (![A_181, B_182]: (v1_funct_1(k7_tmap_1(A_181, B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.30/2.03  tff(c_398, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_388])).
% 5.30/2.03  tff(c_403, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_398])).
% 5.30/2.03  tff(c_404, plain, (v1_funct_1(k7_tmap_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_403])).
% 5.30/2.03  tff(c_48, plain, (![A_38, B_39]: (m1_subset_1(k7_tmap_1(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(k6_tmap_1(A_38, B_39))))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.30/2.03  tff(c_1472, plain, (![B_306, D_309, C_308, A_310, F_307]: (r1_tmap_1(D_309, A_310, k2_tmap_1(B_306, A_310, C_308, D_309), F_307) | ~r1_tmap_1(B_306, A_310, C_308, F_307) | ~m1_subset_1(F_307, u1_struct_0(D_309)) | ~m1_subset_1(F_307, u1_struct_0(B_306)) | ~m1_pre_topc(D_309, B_306) | v2_struct_0(D_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_306), u1_struct_0(A_310)))) | ~v1_funct_2(C_308, u1_struct_0(B_306), u1_struct_0(A_310)) | ~v1_funct_1(C_308) | ~l1_pre_topc(B_306) | ~v2_pre_topc(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_223])).
% 5.30/2.03  tff(c_2329, plain, (![D_417, A_418, B_419, F_420]: (r1_tmap_1(D_417, k6_tmap_1(A_418, B_419), k2_tmap_1(A_418, k6_tmap_1(A_418, B_419), k7_tmap_1(A_418, B_419), D_417), F_420) | ~r1_tmap_1(A_418, k6_tmap_1(A_418, B_419), k7_tmap_1(A_418, B_419), F_420) | ~m1_subset_1(F_420, u1_struct_0(D_417)) | ~m1_subset_1(F_420, u1_struct_0(A_418)) | ~m1_pre_topc(D_417, A_418) | v2_struct_0(D_417) | ~v1_funct_2(k7_tmap_1(A_418, B_419), u1_struct_0(A_418), u1_struct_0(k6_tmap_1(A_418, B_419))) | ~v1_funct_1(k7_tmap_1(A_418, B_419)) | ~l1_pre_topc(k6_tmap_1(A_418, B_419)) | ~v2_pre_topc(k6_tmap_1(A_418, B_419)) | v2_struct_0(k6_tmap_1(A_418, B_419)) | ~m1_subset_1(B_419, k1_zfmisc_1(u1_struct_0(A_418))) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(resolution, [status(thm)], [c_48, c_1472])).
% 5.30/2.03  tff(c_64, plain, (~r1_tmap_1('#skF_7', k6_tmap_1('#skF_5', '#skF_6'), k2_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_247])).
% 5.30/2.03  tff(c_2332, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k7_tmap_1('#skF_5', '#skF_6')) | ~l1_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | ~v2_pre_topc(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2329, c_64])).
% 5.30/2.03  tff(c_2335, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_7') | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6'))) | v2_struct_0(k6_tmap_1('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_777, c_544, c_404, c_70, c_66, c_2332])).
% 5.30/2.03  tff(c_2336, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_676, c_72, c_2335])).
% 5.30/2.03  tff(c_2408, plain, (~v1_funct_2(k7_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_2336])).
% 5.30/2.03  tff(c_2411, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2408])).
% 5.30/2.03  tff(c_2414, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2411])).
% 5.30/2.03  tff(c_2416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2414])).
% 5.30/2.03  tff(c_2417, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_2336])).
% 5.30/2.03  tff(c_2432, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_2417])).
% 5.30/2.03  tff(c_2435, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2432])).
% 5.30/2.03  tff(c_2438, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2435])).
% 5.30/2.03  tff(c_2439, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_355, c_2438])).
% 5.30/2.03  tff(c_2461, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_993, c_2439])).
% 5.30/2.03  tff(c_2464, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_2461])).
% 5.30/2.03  tff(c_2466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2464])).
% 5.30/2.03  tff(c_2467, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2417])).
% 5.30/2.03  tff(c_2471, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_993, c_2467])).
% 5.30/2.03  tff(c_2474, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_2471])).
% 5.30/2.03  tff(c_2476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2474])).
% 5.30/2.03  tff(c_2478, plain, (r1_tarski(u1_struct_0('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_258])).
% 5.30/2.03  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.30/2.03  tff(c_2589, plain, (![A_444, B_445, B_446]: (r2_hidden('#skF_3'(A_444, B_445), B_446) | ~r1_tarski(A_444, B_446) | r1_xboole_0(A_444, B_445))), inference(resolution, [status(thm)], [c_16, c_192])).
% 5.30/2.03  tff(c_232, plain, (![B_11]: (~r2_hidden('#skF_3'(u1_struct_0('#skF_7'), B_11), '#skF_6') | r1_xboole_0(u1_struct_0('#skF_7'), B_11))), inference(resolution, [status(thm)], [c_16, c_208])).
% 5.30/2.03  tff(c_2593, plain, (![B_445]: (~r1_tarski(u1_struct_0('#skF_7'), '#skF_6') | r1_xboole_0(u1_struct_0('#skF_7'), B_445))), inference(resolution, [status(thm)], [c_2589, c_232])).
% 5.30/2.03  tff(c_2617, plain, (![B_447]: (r1_xboole_0(u1_struct_0('#skF_7'), B_447))), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_2593])).
% 5.30/2.03  tff(c_12, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, B_11) | ~r2_hidden(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.30/2.03  tff(c_2659, plain, (![C_452, B_453]: (~r2_hidden(C_452, B_453) | ~r2_hidden(C_452, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_2617, c_12])).
% 5.30/2.03  tff(c_2681, plain, (![A_454]: (~r2_hidden('#skF_1'(A_454), u1_struct_0('#skF_7')) | v1_xboole_0(A_454))), inference(resolution, [status(thm)], [c_4, c_2659])).
% 5.30/2.03  tff(c_2693, plain, (![A_1]: (~r1_tarski(A_1, u1_struct_0('#skF_7')) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_207, c_2681])).
% 5.30/2.03  tff(c_3084, plain, (v1_xboole_0('#skF_4'('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3064, c_2693])).
% 5.30/2.03  tff(c_3110, plain, (v1_xboole_0('#skF_4'('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_100, c_3084])).
% 5.30/2.03  tff(c_3111, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_3110])).
% 5.30/2.03  tff(c_38, plain, (![A_34]: (~v1_xboole_0('#skF_4'(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.30/2.03  tff(c_3122, plain, (~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3111, c_38])).
% 5.30/2.03  tff(c_3127, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_100, c_3122])).
% 5.30/2.03  tff(c_3129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3127])).
% 5.30/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/2.03  
% 5.30/2.03  Inference rules
% 5.30/2.03  ----------------------
% 5.30/2.03  #Ref     : 0
% 5.30/2.03  #Sup     : 613
% 5.30/2.03  #Fact    : 0
% 5.30/2.03  #Define  : 0
% 5.30/2.03  #Split   : 18
% 5.30/2.03  #Chain   : 0
% 5.30/2.03  #Close   : 0
% 5.30/2.03  
% 5.30/2.03  Ordering : KBO
% 5.30/2.03  
% 5.30/2.03  Simplification rules
% 5.30/2.03  ----------------------
% 5.30/2.03  #Subsume      : 233
% 5.30/2.03  #Demod        : 152
% 5.30/2.03  #Tautology    : 75
% 5.30/2.03  #SimpNegUnit  : 92
% 5.30/2.03  #BackRed      : 0
% 5.30/2.03  
% 5.30/2.03  #Partial instantiations: 0
% 5.30/2.03  #Strategies tried      : 1
% 5.30/2.03  
% 5.30/2.03  Timing (in seconds)
% 5.30/2.03  ----------------------
% 5.30/2.03  Preprocessing        : 0.36
% 5.30/2.03  Parsing              : 0.20
% 5.30/2.03  CNF conversion       : 0.03
% 5.30/2.03  Main loop            : 0.85
% 5.30/2.03  Inferencing          : 0.29
% 5.30/2.03  Reduction            : 0.23
% 5.30/2.03  Demodulation         : 0.14
% 5.30/2.03  BG Simplification    : 0.03
% 5.30/2.03  Subsumption          : 0.24
% 5.30/2.03  Abstraction          : 0.03
% 5.30/2.03  MUC search           : 0.00
% 5.30/2.03  Cooper               : 0.00
% 5.30/2.03  Total                : 1.25
% 5.30/2.03  Index Insertion      : 0.00
% 5.30/2.03  Index Deletion       : 0.00
% 5.30/2.03  Index Matching       : 0.00
% 5.30/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
