%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1592+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:07 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  189 (1556 expanded)
%              Number of leaves         :   49 ( 577 expanded)
%              Depth                    :   20
%              Number of atoms          :  563 (9371 expanded)
%              Number of equality atoms :   53 (1654 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_yellow_0 > v4_yellow_0 > r2_hidden > r1_yellow_0 > m1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k13_lattice3 > k2_tarski > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v6_yellow_0,type,(
    v6_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_261,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & v6_yellow_0(B,A)
              & m1_yellow_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(A))
                           => ( ( E = C
                                & F = D )
                             => k13_lattice3(B,C,D) = k13_lattice3(A,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_yellow_0)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_178,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
           => ( v3_orders_2(B)
              & v4_yellow_0(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_yellow_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
           => ( v4_orders_2(B)
              & v4_yellow_0(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc7_yellow_0)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
           => ( v5_orders_2(B)
              & v4_yellow_0(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_yellow_0)).

tff(f_172,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

tff(f_196,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k1_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k13_lattice3(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_0)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v6_yellow_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,u1_struct_0(B))
                        & r2_hidden(D,u1_struct_0(B))
                        & r1_yellow_0(A,k7_domain_1(u1_struct_0(A),C,D)) )
                     => r2_hidden(k1_yellow_0(A,k7_domain_1(u1_struct_0(A),C,D)),u1_struct_0(B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_222,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( ( r1_yellow_0(A,C)
                  & r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) )
               => ( r1_yellow_0(B,C)
                  & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_yellow_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_yellow_0(B,A)
              & v6_yellow_0(B,A) )
           => ( ~ v2_struct_0(B)
              & v1_lattice3(B)
              & v4_yellow_0(B,A)
              & v6_yellow_0(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc12_yellow_0)).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_86,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_78,plain,(
    m1_yellow_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_108,plain,(
    ! [B_136,A_137] :
      ( l1_orders_2(B_136)
      | ~ m1_yellow_0(B_136,A_137)
      | ~ l1_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_111,plain,
    ( l1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_108])).

tff(c_114,plain,(
    l1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_111])).

tff(c_40,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_141,plain,(
    ! [A_150,B_151,C_152] :
      ( k7_domain_1(A_150,B_151,C_152) = k2_tarski(B_151,C_152)
      | ~ m1_subset_1(C_152,A_150)
      | ~ m1_subset_1(B_151,A_150)
      | v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_159,plain,(
    ! [B_151] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_151,'#skF_8') = k2_tarski(B_151,'#skF_8')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_74,c_141])).

tff(c_164,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_44,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_167,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_164,c_44])).

tff(c_170,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_167])).

tff(c_174,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_174])).

tff(c_180,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_56,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_80,plain,(
    v6_yellow_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_68,plain,(
    '#skF_7' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_95,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_76])).

tff(c_82,plain,(
    v4_yellow_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_94,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_119,plain,(
    ! [B_143,A_144] :
      ( v3_orders_2(B_143)
      | ~ v4_yellow_0(B_143,A_144)
      | ~ m1_yellow_0(B_143,A_144)
      | ~ l1_orders_2(A_144)
      | ~ v3_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_122,plain,
    ( v3_orders_2('#skF_6')
    | ~ m1_yellow_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_119])).

tff(c_125,plain,(
    v3_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_86,c_78,c_122])).

tff(c_92,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_133,plain,(
    ! [B_147,A_148] :
      ( v4_orders_2(B_147)
      | ~ v4_yellow_0(B_147,A_148)
      | ~ m1_yellow_0(B_147,A_148)
      | ~ l1_orders_2(A_148)
      | ~ v4_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_136,plain,
    ( v4_orders_2('#skF_6')
    | ~ m1_yellow_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_133])).

tff(c_139,plain,(
    v4_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_86,c_78,c_136])).

tff(c_90,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_126,plain,(
    ! [B_145,A_146] :
      ( v5_orders_2(B_145)
      | ~ v4_yellow_0(B_145,A_146)
      | ~ m1_yellow_0(B_145,A_146)
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_129,plain,
    ( v5_orders_2('#skF_6')
    | ~ m1_yellow_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_126])).

tff(c_132,plain,(
    v5_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_78,c_129])).

tff(c_52,plain,(
    ! [A_50] :
      ( m1_subset_1('#skF_4'(A_50),u1_struct_0(A_50))
      | v1_lattice3(A_50)
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_181,plain,(
    ! [B_158] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_158,'#skF_8') = k2_tarski(B_158,'#skF_8')
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_189,plain,
    ( k7_domain_1(u1_struct_0('#skF_6'),'#skF_4'('#skF_6'),'#skF_8') = k2_tarski('#skF_4'('#skF_6'),'#skF_8')
    | v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_181])).

tff(c_201,plain,
    ( k7_domain_1(u1_struct_0('#skF_6'),'#skF_4'('#skF_6'),'#skF_8') = k2_tarski('#skF_4'('#skF_6'),'#skF_8')
    | v1_lattice3('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_114,c_189])).

tff(c_230,plain,(
    v1_lattice3('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_158,plain,(
    ! [B_151] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_151,'#skF_9') = k2_tarski(B_151,'#skF_9')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_95,c_141])).

tff(c_245,plain,(
    ! [B_161] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_161,'#skF_9') = k2_tarski(B_161,'#skF_9')
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_158])).

tff(c_274,plain,(
    k7_domain_1(u1_struct_0('#skF_6'),'#skF_9','#skF_9') = k2_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_95,c_245])).

tff(c_671,plain,(
    ! [A_198,B_199,C_200] :
      ( k1_yellow_0(A_198,k7_domain_1(u1_struct_0(A_198),B_199,C_200)) = k13_lattice3(A_198,B_199,C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ m1_subset_1(B_199,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | ~ v1_lattice3(A_198)
      | ~ v5_orders_2(A_198)
      | ~ v4_orders_2(A_198)
      | ~ v3_orders_2(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_723,plain,
    ( k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_6','#skF_9','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_671])).

tff(c_759,plain,(
    k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_6','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_139,c_132,c_230,c_114,c_95,c_95,c_723])).

tff(c_38,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k7_domain_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,A_39)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_279,plain,
    ( m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_38])).

tff(c_283,plain,
    ( m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_279])).

tff(c_284,plain,(
    m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_283])).

tff(c_88,plain,(
    v1_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_456,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1('#skF_2'(A_169,B_170),u1_struct_0(A_169))
      | v6_yellow_0(B_170,A_169)
      | ~ m1_yellow_0(B_170,A_169)
      | ~ l1_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_157,plain,(
    ! [B_151] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_151,'#skF_9') = k2_tarski(B_151,'#skF_9')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72,c_141])).

tff(c_302,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_306,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_302,c_44])).

tff(c_307,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_311,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_307])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_311])).

tff(c_316,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_10,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_320,plain,
    ( ~ v1_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_316,c_10])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_320])).

tff(c_325,plain,(
    ! [B_151] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_151,'#skF_9') = k2_tarski(B_151,'#skF_9')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_464,plain,(
    ! [B_170] :
      ( k7_domain_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5',B_170),'#skF_9') = k2_tarski('#skF_2'('#skF_5',B_170),'#skF_9')
      | v6_yellow_0(B_170,'#skF_5')
      | ~ m1_yellow_0(B_170,'#skF_5')
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_456,c_325])).

tff(c_480,plain,(
    ! [B_170] :
      ( k7_domain_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5',B_170),'#skF_9') = k2_tarski('#skF_2'('#skF_5',B_170),'#skF_9')
      | v6_yellow_0(B_170,'#skF_5')
      | ~ m1_yellow_0(B_170,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_464])).

tff(c_542,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_549,plain,
    ( ~ v1_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_542,c_10])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_88,c_549])).

tff(c_555,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_48,plain,(
    ! [A_50,B_57,C_59] :
      ( r1_yellow_0(A_50,k2_tarski(B_57,C_59))
      | ~ m1_subset_1(C_59,u1_struct_0(A_50))
      | ~ m1_subset_1(B_57,u1_struct_0(A_50))
      | ~ v1_lattice3(A_50)
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_342,plain,(
    ! [B_165] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_165,'#skF_9') = k2_tarski(B_165,'#skF_9')
      | ~ m1_subset_1(B_165,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_371,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_9') = k2_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_342])).

tff(c_711,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_5','#skF_9','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_671])).

tff(c_751,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_5','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_72,c_72,c_711])).

tff(c_1093,plain,(
    ! [A_221,C_222,D_223,B_224] :
      ( r2_hidden(k1_yellow_0(A_221,k7_domain_1(u1_struct_0(A_221),C_222,D_223)),u1_struct_0(B_224))
      | ~ r1_yellow_0(A_221,k7_domain_1(u1_struct_0(A_221),C_222,D_223))
      | ~ r2_hidden(D_223,u1_struct_0(B_224))
      | ~ r2_hidden(C_222,u1_struct_0(B_224))
      | ~ m1_subset_1(D_223,u1_struct_0(A_221))
      | ~ m1_subset_1(C_222,u1_struct_0(A_221))
      | ~ v6_yellow_0(B_224,A_221)
      | ~ m1_yellow_0(B_224,A_221)
      | ~ l1_orders_2(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1142,plain,(
    ! [B_224] :
      ( r2_hidden(k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9')),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_9'))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5')
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1093])).

tff(c_1192,plain,(
    ! [B_224] :
      ( r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_9'),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9'))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_72,c_72,c_371,c_751,c_1142])).

tff(c_1193,plain,(
    ! [B_224] :
      ( r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_9'),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9'))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_1192])).

tff(c_1246,plain,(
    ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1193])).

tff(c_1249,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ v1_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1246])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_88,c_72,c_1249])).

tff(c_1255,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1193])).

tff(c_60,plain,(
    ! [B_74,C_76,A_70] :
      ( k1_yellow_0(B_74,C_76) = k1_yellow_0(A_70,C_76)
      | ~ r2_hidden(k1_yellow_0(A_70,C_76),u1_struct_0(B_74))
      | ~ r1_yellow_0(A_70,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(B_74)))
      | ~ m1_yellow_0(B_74,A_70)
      | ~ v4_yellow_0(B_74,A_70)
      | v2_struct_0(B_74)
      | ~ l1_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_2702,plain,(
    ! [B_318,A_319,C_320,D_321] :
      ( k1_yellow_0(B_318,k7_domain_1(u1_struct_0(A_319),C_320,D_321)) = k1_yellow_0(A_319,k7_domain_1(u1_struct_0(A_319),C_320,D_321))
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(A_319),C_320,D_321),k1_zfmisc_1(u1_struct_0(B_318)))
      | ~ v4_yellow_0(B_318,A_319)
      | v2_struct_0(B_318)
      | ~ v4_orders_2(A_319)
      | ~ r1_yellow_0(A_319,k7_domain_1(u1_struct_0(A_319),C_320,D_321))
      | ~ r2_hidden(D_321,u1_struct_0(B_318))
      | ~ r2_hidden(C_320,u1_struct_0(B_318))
      | ~ m1_subset_1(D_321,u1_struct_0(A_319))
      | ~ m1_subset_1(C_320,u1_struct_0(A_319))
      | ~ v6_yellow_0(B_318,A_319)
      | ~ m1_yellow_0(B_318,A_319)
      | ~ l1_orders_2(A_319)
      | v2_struct_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_1093,c_60])).

tff(c_2730,plain,(
    ! [B_318] :
      ( k1_yellow_0(B_318,k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_9')) = k1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_9'))
      | ~ m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0(B_318)))
      | ~ v4_yellow_0(B_318,'#skF_5')
      | v2_struct_0(B_318)
      | ~ v4_orders_2('#skF_5')
      | ~ r1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_9'))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_318))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_318))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ v6_yellow_0(B_318,'#skF_5')
      | ~ m1_yellow_0(B_318,'#skF_5')
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_2702])).

tff(c_2774,plain,(
    ! [B_318] :
      ( k1_yellow_0(B_318,k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_5','#skF_9','#skF_9')
      | ~ m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0(B_318)))
      | ~ v4_yellow_0(B_318,'#skF_5')
      | v2_struct_0(B_318)
      | ~ r2_hidden('#skF_9',u1_struct_0(B_318))
      | ~ v6_yellow_0(B_318,'#skF_5')
      | ~ m1_yellow_0(B_318,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_72,c_72,c_1255,c_371,c_92,c_751,c_371,c_371,c_2730])).

tff(c_2796,plain,(
    ! [B_322] :
      ( k1_yellow_0(B_322,k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_5','#skF_9','#skF_9')
      | ~ m1_subset_1(k2_tarski('#skF_9','#skF_9'),k1_zfmisc_1(u1_struct_0(B_322)))
      | ~ v4_yellow_0(B_322,'#skF_5')
      | v2_struct_0(B_322)
      | ~ r2_hidden('#skF_9',u1_struct_0(B_322))
      | ~ v6_yellow_0(B_322,'#skF_5')
      | ~ m1_yellow_0(B_322,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_2774])).

tff(c_2802,plain,
    ( k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_9')) = k13_lattice3('#skF_5','#skF_9','#skF_9')
    | ~ v4_yellow_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_6'))
    | ~ v6_yellow_0('#skF_6','#skF_5')
    | ~ m1_yellow_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_284,c_2796])).

tff(c_2808,plain,
    ( k13_lattice3('#skF_5','#skF_9','#skF_9') = k13_lattice3('#skF_6','#skF_9','#skF_9')
    | v2_struct_0('#skF_6')
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_82,c_759,c_2802])).

tff(c_2809,plain,
    ( k13_lattice3('#skF_5','#skF_9','#skF_9') = k13_lattice3('#skF_6','#skF_9','#skF_9')
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2808])).

tff(c_2810,plain,(
    ~ r2_hidden('#skF_9',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2809])).

tff(c_2813,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_2810])).

tff(c_2816,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_2813])).

tff(c_2818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_2816])).

tff(c_2820,plain,(
    r2_hidden('#skF_9',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2809])).

tff(c_66,plain,(
    '#skF_10' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70])).

tff(c_326,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_156,plain,(
    ! [B_151] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_151,'#skF_8') = k2_tarski(B_151,'#skF_8')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_96,c_141])).

tff(c_400,plain,(
    ! [B_168] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_168,'#skF_8') = k2_tarski(B_168,'#skF_8')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_156])).

tff(c_429,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_8') = k2_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_400])).

tff(c_705,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_671])).

tff(c_747,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_5','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_72,c_96,c_705])).

tff(c_1136,plain,(
    ! [B_224] :
      ( r2_hidden(k1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8')),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_8'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_224))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5')
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_1093])).

tff(c_1186,plain,(
    ! [B_224] :
      ( r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_224))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_72,c_96,c_429,c_747,c_1136])).

tff(c_1187,plain,(
    ! [B_224] :
      ( r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_224))
      | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_224))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_1186])).

tff(c_1393,plain,(
    ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1426,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ v1_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1393])).

tff(c_1430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_88,c_72,c_96,c_1426])).

tff(c_1431,plain,(
    ! [B_224] :
      ( r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_224))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_224))
      | ~ r2_hidden('#skF_9',u1_struct_0(B_224))
      | ~ v6_yellow_0(B_224,'#skF_5')
      | ~ m1_yellow_0(B_224,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_64,plain,(
    k13_lattice3('#skF_5','#skF_9','#skF_10') != k13_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_97,plain,(
    k13_lattice3('#skF_5','#skF_9','#skF_8') != k13_lattice3('#skF_6','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64])).

tff(c_202,plain,(
    k7_domain_1(u1_struct_0('#skF_6'),'#skF_9','#skF_8') = k2_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_95,c_181])).

tff(c_726,plain,
    ( k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_6','#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6')
    | ~ v1_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_671])).

tff(c_761,plain,(
    k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_6','#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_139,c_132,c_230,c_114,c_95,c_74,c_726])).

tff(c_220,plain,
    ( m1_subset_1(k2_tarski('#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_38])).

tff(c_224,plain,
    ( m1_subset_1(k2_tarski('#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_74,c_220])).

tff(c_225,plain,(
    m1_subset_1(k2_tarski('#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_224])).

tff(c_1432,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_58,plain,(
    ! [A_63,B_67,C_69] :
      ( k1_yellow_0(A_63,k7_domain_1(u1_struct_0(A_63),B_67,C_69)) = k13_lattice3(A_63,B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_63))
      | ~ m1_subset_1(B_67,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | ~ v1_lattice3(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_927,plain,(
    ! [B_211,C_212,A_213] :
      ( k1_yellow_0(B_211,C_212) = k1_yellow_0(A_213,C_212)
      | ~ r2_hidden(k1_yellow_0(A_213,C_212),u1_struct_0(B_211))
      | ~ r1_yellow_0(A_213,C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(u1_struct_0(B_211)))
      | ~ m1_yellow_0(B_211,A_213)
      | ~ v4_yellow_0(B_211,A_213)
      | v2_struct_0(B_211)
      | ~ l1_orders_2(A_213)
      | ~ v4_orders_2(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_2874,plain,(
    ! [B_325,A_326,B_327,C_328] :
      ( k1_yellow_0(B_325,k7_domain_1(u1_struct_0(A_326),B_327,C_328)) = k1_yellow_0(A_326,k7_domain_1(u1_struct_0(A_326),B_327,C_328))
      | ~ r2_hidden(k13_lattice3(A_326,B_327,C_328),u1_struct_0(B_325))
      | ~ r1_yellow_0(A_326,k7_domain_1(u1_struct_0(A_326),B_327,C_328))
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(A_326),B_327,C_328),k1_zfmisc_1(u1_struct_0(B_325)))
      | ~ m1_yellow_0(B_325,A_326)
      | ~ v4_yellow_0(B_325,A_326)
      | v2_struct_0(B_325)
      | ~ l1_orders_2(A_326)
      | ~ v4_orders_2(A_326)
      | v2_struct_0(A_326)
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ m1_subset_1(B_327,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326)
      | ~ v1_lattice3(A_326)
      | ~ v5_orders_2(A_326)
      | ~ v4_orders_2(A_326)
      | ~ v3_orders_2(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_927])).

tff(c_2900,plain,(
    ! [B_325] :
      ( k1_yellow_0(B_325,k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_8')) = k1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_8'))
      | ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_325))
      | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_9','#skF_8'))
      | ~ m1_subset_1(k7_domain_1(u1_struct_0('#skF_5'),'#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0(B_325)))
      | ~ m1_yellow_0(B_325,'#skF_5')
      | ~ v4_yellow_0(B_325,'#skF_5')
      | v2_struct_0(B_325)
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_2874])).

tff(c_2940,plain,(
    ! [B_325] :
      ( k1_yellow_0(B_325,k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_5','#skF_9','#skF_8')
      | ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_325))
      | ~ m1_subset_1(k2_tarski('#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0(B_325)))
      | ~ m1_yellow_0(B_325,'#skF_5')
      | ~ v4_yellow_0(B_325,'#skF_5')
      | v2_struct_0(B_325)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_72,c_96,c_92,c_86,c_429,c_1432,c_747,c_429,c_429,c_2900])).

tff(c_3007,plain,(
    ! [B_332] :
      ( k1_yellow_0(B_332,k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_5','#skF_9','#skF_8')
      | ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0(B_332))
      | ~ m1_subset_1(k2_tarski('#skF_9','#skF_8'),k1_zfmisc_1(u1_struct_0(B_332)))
      | ~ m1_yellow_0(B_332,'#skF_5')
      | ~ v4_yellow_0(B_332,'#skF_5')
      | v2_struct_0(B_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_2940])).

tff(c_3013,plain,
    ( k1_yellow_0('#skF_6',k2_tarski('#skF_9','#skF_8')) = k13_lattice3('#skF_5','#skF_9','#skF_8')
    | ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0('#skF_6'))
    | ~ m1_yellow_0('#skF_6','#skF_5')
    | ~ v4_yellow_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_225,c_3007])).

tff(c_3019,plain,
    ( k13_lattice3('#skF_5','#skF_9','#skF_8') = k13_lattice3('#skF_6','#skF_9','#skF_8')
    | ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_761,c_3013])).

tff(c_3020,plain,(
    ~ r2_hidden(k13_lattice3('#skF_5','#skF_9','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_97,c_3019])).

tff(c_3023,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_6'))
    | ~ v6_yellow_0('#skF_6','#skF_5')
    | ~ m1_yellow_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1431,c_3020])).

tff(c_3029,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80,c_2820,c_3023])).

tff(c_3034,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_3029])).

tff(c_3037,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3034])).

tff(c_3039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_3037])).

tff(c_3041,plain,(
    ~ v1_lattice3('#skF_6') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_3533,plain,(
    ! [B_357,A_358] :
      ( v1_lattice3(B_357)
      | ~ v6_yellow_0(B_357,A_358)
      | ~ v4_yellow_0(B_357,A_358)
      | v2_struct_0(B_357)
      | ~ m1_yellow_0(B_357,A_358)
      | ~ l1_orders_2(A_358)
      | ~ v1_lattice3(A_358)
      | ~ v5_orders_2(A_358)
      | ~ v4_orders_2(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3536,plain,
    ( v1_lattice3('#skF_6')
    | ~ v4_yellow_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ m1_yellow_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_3533])).

tff(c_3539,plain,
    ( v1_lattice3('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_78,c_82,c_3536])).

tff(c_3541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3041,c_3539])).

%------------------------------------------------------------------------------
