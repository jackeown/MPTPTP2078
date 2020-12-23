%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:44 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  228 (10252 expanded)
%              Number of leaves         :   49 (3321 expanded)
%              Depth                    :   33
%              Number of atoms          :  732 (69571 expanded)
%              Number of equality atoms :  133 (8442 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_waybel_7 > v1_waybel_0 > v13_waybel_0 > v12_waybel_0 > r2_yellow_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k12_lattice3 > k2_zfmisc_1 > k2_yellow_0 > k2_tarski > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_241,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v3_orders_2(B)
              & v4_orders_2(B)
              & v5_orders_2(B)
              & v1_lattice3(B)
              & v2_lattice3(B)
              & l1_orders_2(B) )
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v1_waybel_0(C,A)
                    & v12_waybel_0(C,A)
                    & v1_waybel_7(C,A)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
                 => ( ~ v1_xboole_0(C)
                    & v1_waybel_0(C,B)
                    & v12_waybel_0(C,B)
                    & v1_waybel_7(C,B)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_7)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( C = D
                        & v1_waybel_0(C,A) )
                     => v1_waybel_0(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_0)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( ( v12_waybel_0(C,A)
                         => v12_waybel_0(D,B) )
                        & ( v13_waybel_0(C,A)
                         => v13_waybel_0(D,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(k12_lattice3(A,C,D),B)
                        & ~ r2_hidden(C,B)
                        & ~ r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_7)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_190,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k2_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k12_lattice3(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r2_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_0)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( r2_yellow_0(A,C)
               => k2_yellow_0(A,C) = k2_yellow_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(c_74,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_76,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_62,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_20,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_orders_2(A_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(A_30))))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_636,plain,(
    ! [D_180,B_181,C_182,A_183] :
      ( D_180 = B_181
      | g1_orders_2(C_182,D_180) != g1_orders_2(A_183,B_181)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_641,plain,(
    ! [B_184,A_185] :
      ( u1_orders_2('#skF_5') = B_184
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_185,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_636])).

tff(c_645,plain,(
    ! [A_30] :
      ( u1_orders_2(A_30) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_30),u1_orders_2(A_30)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_641])).

tff(c_664,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_645])).

tff(c_666,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_664])).

tff(c_681,plain,
    ( m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_20])).

tff(c_685,plain,(
    m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_681])).

tff(c_677,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_60])).

tff(c_26,plain,(
    ! [C_36,A_32,D_37,B_33] :
      ( C_36 = A_32
      | g1_orders_2(C_36,D_37) != g1_orders_2(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_698,plain,(
    ! [C_36,D_37] :
      ( u1_struct_0('#skF_5') = C_36
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_36,D_37)
      | ~ m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_26])).

tff(c_704,plain,(
    ! [C_36,D_37] :
      ( u1_struct_0('#skF_5') = C_36
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_36,D_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_698])).

tff(c_729,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_704])).

tff(c_134,plain,(
    ! [C_109,A_110,D_111,B_112] :
      ( C_109 = A_110
      | g1_orders_2(C_109,D_111) != g1_orders_2(A_110,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_140,plain,(
    ! [A_113,B_114] :
      ( u1_struct_0('#skF_5') = A_113
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_134])).

tff(c_144,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_30),u1_orders_2(A_30)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_169,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_144])).

tff(c_171,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_169])).

tff(c_149,plain,(
    ! [D_115,B_116,C_117,A_118] :
      ( D_115 = B_116
      | g1_orders_2(C_117,D_115) != g1_orders_2(A_118,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_118,A_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_269,plain,(
    ! [B_130,A_131] :
      ( u1_orders_2('#skF_5') = B_130
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_131,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_131,A_131))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_149])).

tff(c_280,plain,(
    ! [A_30] :
      ( u1_orders_2(A_30) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_30),u1_orders_2(A_30)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_269])).

tff(c_283,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_280])).

tff(c_285,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_283])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_183,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_50])).

tff(c_56,plain,(
    v1_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v1_waybel_7('#skF_7','#skF_6')
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_85,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v1_waybel_7('#skF_7','#skF_6')
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48])).

tff(c_139,plain,(
    ~ v1_waybel_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_494,plain,(
    ! [D_162,B_163,A_164] :
      ( v1_waybel_0(D_162,B_163)
      | ~ v1_waybel_0(D_162,A_164)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(u1_struct_0(B_163)))
      | ~ m1_subset_1(D_162,k1_zfmisc_1(u1_struct_0(A_164)))
      | g1_orders_2(u1_struct_0(B_163),u1_orders_2(B_163)) != g1_orders_2(u1_struct_0(A_164),u1_orders_2(A_164))
      | ~ l1_orders_2(B_163)
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_496,plain,(
    ! [A_164] :
      ( v1_waybel_0('#skF_7','#skF_6')
      | ~ v1_waybel_0('#skF_7',A_164)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_164)))
      | g1_orders_2(u1_struct_0(A_164),u1_orders_2(A_164)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ l1_orders_2(A_164) ) ),
    inference(resolution,[status(thm)],[c_183,c_494])).

tff(c_501,plain,(
    ! [A_164] :
      ( v1_waybel_0('#skF_7','#skF_6')
      | ~ v1_waybel_0('#skF_7',A_164)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_164)))
      | g1_orders_2(u1_struct_0(A_164),u1_orders_2(A_164)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_496])).

tff(c_505,plain,(
    ! [A_165] :
      ( ~ v1_waybel_0('#skF_7',A_165)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_165)))
      | g1_orders_2(u1_struct_0(A_165),u1_orders_2(A_165)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_501])).

tff(c_509,plain,
    ( ~ v1_waybel_0('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_505])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_171,c_285,c_183,c_56,c_509])).

tff(c_516,plain,
    ( ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_518,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_598,plain,(
    ! [A_177,B_178] :
      ( u1_struct_0('#skF_5') = A_177
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k2_zfmisc_1(A_177,A_177))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_134])).

tff(c_609,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_30),u1_orders_2(A_30)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_598])).

tff(c_612,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_609])).

tff(c_614,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_612])).

tff(c_626,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_50])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_626])).

tff(c_630,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_54,plain,(
    v12_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_629,plain,
    ( ~ v1_waybel_7('#skF_7','#skF_6')
    | ~ v12_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_631,plain,(
    ~ v12_waybel_0('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_919,plain,(
    ! [D_222,B_223,A_224] :
      ( v12_waybel_0(D_222,B_223)
      | ~ v12_waybel_0(D_222,A_224)
      | ~ m1_subset_1(D_222,k1_zfmisc_1(u1_struct_0(B_223)))
      | ~ m1_subset_1(D_222,k1_zfmisc_1(u1_struct_0(A_224)))
      | g1_orders_2(u1_struct_0(B_223),u1_orders_2(B_223)) != g1_orders_2(u1_struct_0(A_224),u1_orders_2(A_224))
      | ~ l1_orders_2(B_223)
      | ~ l1_orders_2(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_923,plain,(
    ! [A_224] :
      ( v12_waybel_0('#skF_7','#skF_6')
      | ~ v12_waybel_0('#skF_7',A_224)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_224)))
      | g1_orders_2(u1_struct_0(A_224),u1_orders_2(A_224)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ l1_orders_2(A_224) ) ),
    inference(resolution,[status(thm)],[c_630,c_919])).

tff(c_928,plain,(
    ! [A_224] :
      ( v12_waybel_0('#skF_7','#skF_6')
      | ~ v12_waybel_0('#skF_7',A_224)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_224)))
      | g1_orders_2(u1_struct_0(A_224),u1_orders_2(A_224)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_923])).

tff(c_930,plain,(
    ! [A_225] :
      ( ~ v12_waybel_0('#skF_7',A_225)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_225)))
      | g1_orders_2(u1_struct_0(A_225),u1_orders_2(A_225)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_928])).

tff(c_932,plain,
    ( ~ v12_waybel_0('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_930])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_666,c_729,c_630,c_54,c_932])).

tff(c_938,plain,(
    ~ v1_waybel_7('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_72,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_70,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_68,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_64,plain,(
    v2_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_517,plain,(
    v1_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_939,plain,(
    v12_waybel_0('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_52,plain,(
    v1_waybel_7('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_12,plain,(
    ! [A_4,B_18] :
      ( r2_hidden(k12_lattice3(A_4,'#skF_1'(A_4,B_18),'#skF_2'(A_4,B_18)),B_18)
      | v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_82,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_80,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_944,plain,(
    ! [D_226,B_227,C_228,A_229] :
      ( D_226 = B_227
      | g1_orders_2(C_228,D_226) != g1_orders_2(A_229,B_227)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_965,plain,(
    ! [B_233,A_234] :
      ( u1_orders_2('#skF_5') = B_233
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(A_234,B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(k2_zfmisc_1(A_234,A_234))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_944])).

tff(c_969,plain,(
    ! [A_30] :
      ( u1_orders_2(A_30) = u1_orders_2('#skF_5')
      | g1_orders_2(u1_struct_0(A_30),u1_orders_2(A_30)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_965])).

tff(c_977,plain,
    ( u1_orders_2('#skF_5') = u1_orders_2('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_969])).

tff(c_979,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_977])).

tff(c_994,plain,
    ( m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_20])).

tff(c_998,plain,(
    m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_994])).

tff(c_990,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6')) = g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_60])).

tff(c_1016,plain,(
    ! [C_36,D_37] :
      ( u1_struct_0('#skF_5') = C_36
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_36,D_37)
      | ~ m1_subset_1(u1_orders_2('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_26])).

tff(c_1022,plain,(
    ! [C_36,D_37] :
      ( u1_struct_0('#skF_5') = C_36
      | g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6')) != g1_orders_2(C_36,D_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_1016])).

tff(c_1047,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1022])).

tff(c_16,plain,(
    ! [A_4,B_18] :
      ( m1_subset_1('#skF_1'(A_4,B_18),u1_struct_0(A_4))
      | v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1074,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_22])).

tff(c_1086,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1091,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1086])).

tff(c_1095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1091])).

tff(c_1096,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_1098,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_1255,plain,(
    ! [A_279,B_280] :
      ( m1_subset_1('#skF_1'(A_279,B_280),u1_struct_0(A_279))
      | v1_waybel_7(B_280,A_279)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ v12_waybel_0(B_280,A_279)
      | ~ v1_waybel_0(B_280,A_279)
      | v1_xboole_0(B_280)
      | ~ l1_orders_2(A_279)
      | ~ v2_lattice3(A_279)
      | ~ v5_orders_2(A_279)
      | ~ v4_orders_2(A_279)
      | ~ v3_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] :
      ( k7_domain_1(A_38,B_39,C_40) = k2_tarski(B_39,C_40)
      | ~ m1_subset_1(C_40,A_38)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1547,plain,(
    ! [A_320,B_321,B_322] :
      ( k7_domain_1(u1_struct_0(A_320),B_321,'#skF_1'(A_320,B_322)) = k2_tarski(B_321,'#skF_1'(A_320,B_322))
      | ~ m1_subset_1(B_321,u1_struct_0(A_320))
      | v1_xboole_0(u1_struct_0(A_320))
      | v1_waybel_7(B_322,A_320)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ v12_waybel_0(B_322,A_320)
      | ~ v1_waybel_0(B_322,A_320)
      | v1_xboole_0(B_322)
      | ~ l1_orders_2(A_320)
      | ~ v2_lattice3(A_320)
      | ~ v5_orders_2(A_320)
      | ~ v4_orders_2(A_320)
      | ~ v3_orders_2(A_320) ) ),
    inference(resolution,[status(thm)],[c_1255,c_28])).

tff(c_1551,plain,(
    ! [B_321] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_321,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_321,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_321,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | ~ v12_waybel_0('#skF_7','#skF_6')
      | ~ v1_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_630,c_1547])).

tff(c_1557,plain,(
    ! [B_321] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_321,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_321,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_321,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_1551])).

tff(c_1559,plain,(
    ! [B_323] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_323,'#skF_1'('#skF_6','#skF_7')) = k2_tarski(B_323,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_1098,c_1557])).

tff(c_1119,plain,(
    ! [A_250,B_251,C_252] :
      ( k2_yellow_0(A_250,k7_domain_1(u1_struct_0(A_250),B_251,C_252)) = k12_lattice3(A_250,B_251,C_252)
      | ~ m1_subset_1(C_252,u1_struct_0(A_250))
      | ~ m1_subset_1(B_251,u1_struct_0(A_250))
      | ~ l1_orders_2(A_250)
      | ~ v2_lattice3(A_250)
      | ~ v5_orders_2(A_250)
      | ~ v4_orders_2(A_250)
      | ~ v3_orders_2(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1128,plain,(
    ! [B_251,C_252] :
      ( k2_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_6'),B_251,C_252)) = k12_lattice3('#skF_5',B_251,C_252)
      | ~ m1_subset_1(C_252,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_1119])).

tff(c_1132,plain,(
    ! [B_251,C_252] :
      ( k2_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_6'),B_251,C_252)) = k12_lattice3('#skF_5',B_251,C_252)
      | ~ m1_subset_1(C_252,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_76,c_74,c_1047,c_1047,c_1128])).

tff(c_1565,plain,(
    ! [B_323] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_323,'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5',B_323,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_1132])).

tff(c_1607,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1565])).

tff(c_1610,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_1607])).

tff(c_1613,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_630,c_1610])).

tff(c_1615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_1613])).

tff(c_1617,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1565])).

tff(c_14,plain,(
    ! [A_4,B_18] :
      ( m1_subset_1('#skF_2'(A_4,B_18),u1_struct_0(A_4))
      | v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1294,plain,(
    ! [A_284,B_285] :
      ( m1_subset_1('#skF_2'(A_284,B_285),u1_struct_0(A_284))
      | v1_waybel_7(B_285,A_284)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ v12_waybel_0(B_285,A_284)
      | ~ v1_waybel_0(B_285,A_284)
      | v1_xboole_0(B_285)
      | ~ l1_orders_2(A_284)
      | ~ v2_lattice3(A_284)
      | ~ v5_orders_2(A_284)
      | ~ v4_orders_2(A_284)
      | ~ v3_orders_2(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1470,plain,(
    ! [A_315,B_316,B_317] :
      ( k7_domain_1(u1_struct_0(A_315),B_316,'#skF_2'(A_315,B_317)) = k2_tarski(B_316,'#skF_2'(A_315,B_317))
      | ~ m1_subset_1(B_316,u1_struct_0(A_315))
      | v1_xboole_0(u1_struct_0(A_315))
      | v1_waybel_7(B_317,A_315)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ v12_waybel_0(B_317,A_315)
      | ~ v1_waybel_0(B_317,A_315)
      | v1_xboole_0(B_317)
      | ~ l1_orders_2(A_315)
      | ~ v2_lattice3(A_315)
      | ~ v5_orders_2(A_315)
      | ~ v4_orders_2(A_315)
      | ~ v3_orders_2(A_315) ) ),
    inference(resolution,[status(thm)],[c_1294,c_28])).

tff(c_1474,plain,(
    ! [B_316] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_316,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_316,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_316,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | ~ v12_waybel_0('#skF_7','#skF_6')
      | ~ v1_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_630,c_1470])).

tff(c_1480,plain,(
    ! [B_316] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_316,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_316,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_316,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_1474])).

tff(c_1482,plain,(
    ! [B_318] :
      ( k7_domain_1(u1_struct_0('#skF_6'),B_318,'#skF_2'('#skF_6','#skF_7')) = k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_1098,c_1480])).

tff(c_46,plain,(
    ! [A_89,B_93,C_95] :
      ( k2_yellow_0(A_89,k7_domain_1(u1_struct_0(A_89),B_93,C_95)) = k12_lattice3(A_89,B_93,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0(A_89))
      | ~ m1_subset_1(B_93,u1_struct_0(A_89))
      | ~ l1_orders_2(A_89)
      | ~ v2_lattice3(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1491,plain,(
    ! [B_318] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_46])).

tff(c_1497,plain,(
    ! [B_318] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_1491])).

tff(c_1499,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1497])).

tff(c_1502,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_1499])).

tff(c_1505,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_630,c_1502])).

tff(c_1507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_1505])).

tff(c_1509,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_1568,plain,(
    ! [B_323] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_323,'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_323,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_46])).

tff(c_1574,plain,(
    ! [B_323] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_323,'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_323,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_1568])).

tff(c_1699,plain,(
    ! [B_327] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_327,'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_327,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_327,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1617,c_1574])).

tff(c_4,plain,(
    ! [B_3,A_2] : k2_tarski(B_3,A_2) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1530,plain,(
    ! [B_319] :
      ( k2_yellow_0('#skF_6',k2_tarski(B_319,'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6',B_319,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_319,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_1544,plain,(
    ! [B_3] :
      ( k2_yellow_0('#skF_6',k2_tarski('#skF_2'('#skF_6','#skF_7'),B_3)) = k12_lattice3('#skF_6',B_3,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1530])).

tff(c_1706,plain,
    ( k12_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) = k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1699,c_1544])).

tff(c_1724,plain,(
    k12_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) = k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1617,c_1706])).

tff(c_30,plain,(
    ! [A_41,B_48,C_50] :
      ( r2_yellow_0(A_41,k2_tarski(B_48,C_50))
      | ~ m1_subset_1(C_50,u1_struct_0(A_41))
      | ~ m1_subset_1(B_48,u1_struct_0(A_41))
      | ~ v2_lattice3(A_41)
      | ~ l1_orders_2(A_41)
      | ~ v5_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1102,plain,(
    ! [B_245,C_246,A_247] :
      ( k2_yellow_0(B_245,C_246) = k2_yellow_0(A_247,C_246)
      | ~ r2_yellow_0(A_247,C_246)
      | g1_orders_2(u1_struct_0(B_245),u1_orders_2(B_245)) != g1_orders_2(u1_struct_0(A_247),u1_orders_2(A_247))
      | ~ l1_orders_2(B_245)
      | ~ l1_orders_2(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1328,plain,(
    ! [B_293,B_294,C_295,A_296] :
      ( k2_yellow_0(B_293,k2_tarski(B_294,C_295)) = k2_yellow_0(A_296,k2_tarski(B_294,C_295))
      | g1_orders_2(u1_struct_0(B_293),u1_orders_2(B_293)) != g1_orders_2(u1_struct_0(A_296),u1_orders_2(A_296))
      | ~ l1_orders_2(B_293)
      | ~ m1_subset_1(C_295,u1_struct_0(A_296))
      | ~ m1_subset_1(B_294,u1_struct_0(A_296))
      | ~ v2_lattice3(A_296)
      | ~ l1_orders_2(A_296)
      | ~ v5_orders_2(A_296) ) ),
    inference(resolution,[status(thm)],[c_30,c_1102])).

tff(c_1336,plain,(
    ! [B_293,B_294,C_295] :
      ( k2_yellow_0(B_293,k2_tarski(B_294,C_295)) = k2_yellow_0('#skF_5',k2_tarski(B_294,C_295))
      | g1_orders_2(u1_struct_0(B_293),u1_orders_2(B_293)) != g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(B_293)
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_5'))
      | ~ v2_lattice3('#skF_5')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_1328])).

tff(c_1344,plain,(
    ! [B_293,B_294,C_295] :
      ( k2_yellow_0(B_293,k2_tarski(B_294,C_295)) = k2_yellow_0('#skF_5',k2_tarski(B_294,C_295))
      | g1_orders_2(u1_struct_0(B_293),u1_orders_2(B_293)) != g1_orders_2(u1_struct_0('#skF_6'),u1_orders_2('#skF_6'))
      | ~ l1_orders_2(B_293)
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_76,c_1047,c_1047,c_1047,c_1336])).

tff(c_1347,plain,(
    ! [B_294,C_295] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_294,C_295)) = k2_yellow_0('#skF_6',k2_tarski(B_294,C_295))
      | ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_6')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1344])).

tff(c_1349,plain,(
    ! [B_294,C_295] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_294,C_295)) = k2_yellow_0('#skF_6',k2_tarski(B_294,C_295))
      | ~ m1_subset_1(C_295,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1347])).

tff(c_1625,plain,(
    ! [B_325] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_325,'#skF_2'('#skF_6','#skF_7'))) = k2_yellow_0('#skF_6',k2_tarski(B_325,'#skF_2'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1509,c_1349])).

tff(c_1643,plain,(
    ! [A_2] :
      ( k2_yellow_0('#skF_5',k2_tarski('#skF_2'('#skF_6','#skF_7'),A_2)) = k2_yellow_0('#skF_6',k2_tarski(A_2,'#skF_2'('#skF_6','#skF_7')))
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1625])).

tff(c_1780,plain,(
    ! [B_329] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_329,'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5',B_329,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_329,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_329,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1565])).

tff(c_1801,plain,
    ( k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1643,c_1780])).

tff(c_1824,plain,(
    k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1617,c_1509,c_1509,c_1801])).

tff(c_1721,plain,(
    ! [B_3] :
      ( k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),B_3)) = k12_lattice3('#skF_6',B_3,'#skF_1'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_3,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1699])).

tff(c_1830,plain,
    ( k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) = k12_lattice3('#skF_6','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1824,c_1721])).

tff(c_1843,plain,(
    k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) = k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1724,c_1830])).

tff(c_1787,plain,
    ( k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1780,c_1643])).

tff(c_1819,plain,(
    k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1509,c_1617,c_1787])).

tff(c_2009,plain,(
    k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1819])).

tff(c_1365,plain,(
    ! [B_304,C_305] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_304,C_305)) = k2_yellow_0('#skF_6',k2_tarski(B_304,C_305))
      | ~ m1_subset_1(C_305,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1347])).

tff(c_1375,plain,(
    ! [B_304,B_18] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_304,'#skF_1'('#skF_6',B_18))) = k2_yellow_0('#skF_6',k2_tarski(B_304,'#skF_1'('#skF_6',B_18)))
      | ~ m1_subset_1(B_304,u1_struct_0('#skF_6'))
      | v1_waybel_7(B_18,'#skF_6')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_18,'#skF_6')
      | ~ v1_waybel_0(B_18,'#skF_6')
      | v1_xboole_0(B_18)
      | ~ l1_orders_2('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_1365])).

tff(c_1419,plain,(
    ! [B_311,B_312] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_311,'#skF_1'('#skF_6',B_312))) = k2_yellow_0('#skF_6',k2_tarski(B_311,'#skF_1'('#skF_6',B_312)))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_6'))
      | v1_waybel_7(B_312,'#skF_6')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_312,'#skF_6')
      | ~ v1_waybel_0(B_312,'#skF_6')
      | v1_xboole_0(B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_1375])).

tff(c_1421,plain,(
    ! [B_311] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_311,'#skF_1'('#skF_6','#skF_7'))) = k2_yellow_0('#skF_6',k2_tarski(B_311,'#skF_1'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | ~ v12_waybel_0('#skF_7','#skF_6')
      | ~ v1_waybel_0('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_630,c_1419])).

tff(c_1424,plain,(
    ! [B_311] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_311,'#skF_1'('#skF_6','#skF_7'))) = k2_yellow_0('#skF_6',k2_tarski(B_311,'#skF_1'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_6'))
      | v1_waybel_7('#skF_7','#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_939,c_1421])).

tff(c_1426,plain,(
    ! [B_313] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_313,'#skF_1'('#skF_6','#skF_7'))) = k2_yellow_0('#skF_6',k2_tarski(B_313,'#skF_1'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_313,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_1424])).

tff(c_1436,plain,(
    ! [A_2] :
      ( k2_yellow_0('#skF_5',k2_tarski('#skF_1'('#skF_6','#skF_7'),A_2)) = k2_yellow_0('#skF_6',k2_tarski(A_2,'#skF_1'('#skF_6','#skF_7')))
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1426])).

tff(c_1488,plain,(
    ! [B_318] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_318,'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5',B_318,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_1132])).

tff(c_1510,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1488])).

tff(c_1519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1510])).

tff(c_1862,plain,(
    ! [B_330] :
      ( k2_yellow_0('#skF_5',k2_tarski(B_330,'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5',B_330,'#skF_2'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1488])).

tff(c_1890,plain,
    ( k2_yellow_0('#skF_6',k2_tarski('#skF_2'('#skF_6','#skF_7'),'#skF_1'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1436,c_1862])).

tff(c_1908,plain,(
    k2_yellow_0('#skF_6',k2_tarski('#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7'))) = k12_lattice3('#skF_5','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1617,c_1617,c_4,c_1890])).

tff(c_2106,plain,(
    k12_lattice3('#skF_5','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) = k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2009,c_1908])).

tff(c_6,plain,(
    ! [D_27,B_18,C_25,A_4] :
      ( r2_hidden(D_27,B_18)
      | r2_hidden(C_25,B_18)
      | ~ r2_hidden(k12_lattice3(A_4,C_25,D_27),B_18)
      | ~ m1_subset_1(D_27,u1_struct_0(A_4))
      | ~ m1_subset_1(C_25,u1_struct_0(A_4))
      | ~ v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2109,plain,(
    ! [B_18] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_18)
      | r2_hidden('#skF_1'('#skF_6','#skF_7'),B_18)
      | ~ r2_hidden(k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),B_18)
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ v1_waybel_7(B_18,'#skF_5')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_18,'#skF_5')
      | ~ v1_waybel_0(B_18,'#skF_5')
      | v1_xboole_0(B_18)
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_6])).

tff(c_2611,plain,(
    ! [B_348] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_7'),B_348)
      | r2_hidden('#skF_1'('#skF_6','#skF_7'),B_348)
      | ~ r2_hidden(k12_lattice3('#skF_6','#skF_1'('#skF_6','#skF_7'),'#skF_2'('#skF_6','#skF_7')),B_348)
      | ~ v1_waybel_7(B_348,'#skF_5')
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v12_waybel_0(B_348,'#skF_5')
      | ~ v1_waybel_0(B_348,'#skF_5')
      | v1_xboole_0(B_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_76,c_74,c_1047,c_1617,c_1047,c_1509,c_1047,c_2109])).

tff(c_2615,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7')
    | ~ v1_waybel_7('#skF_7','#skF_5')
    | ~ v12_waybel_0('#skF_7','#skF_5')
    | ~ v1_waybel_0('#skF_7','#skF_5')
    | v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_2611])).

tff(c_2618,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7')
    | v1_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_630,c_56,c_54,c_52,c_2615])).

tff(c_2619,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7')
    | r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_2618])).

tff(c_2620,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2619])).

tff(c_10,plain,(
    ! [A_4,B_18] :
      ( ~ r2_hidden('#skF_1'(A_4,B_18),B_18)
      | v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2622,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_2620,c_10])).

tff(c_2625,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_630,c_2622])).

tff(c_2627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_2625])).

tff(c_2628,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2619])).

tff(c_8,plain,(
    ! [A_4,B_18] :
      ( ~ r2_hidden('#skF_2'(A_4,B_18),B_18)
      | v1_waybel_7(B_18,A_4)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ v12_waybel_0(B_18,A_4)
      | ~ v1_waybel_0(B_18,A_4)
      | v1_xboole_0(B_18)
      | ~ l1_orders_2(A_4)
      | ~ v2_lattice3(A_4)
      | ~ v5_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | ~ v3_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2646,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v12_waybel_0('#skF_7','#skF_6')
    | ~ v1_waybel_0('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v2_lattice3('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_2628,c_8])).

tff(c_2649,plain,
    ( v1_waybel_7('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_517,c_939,c_630,c_2646])).

tff(c_2651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_938,c_2649])).

tff(c_2652,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2656,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2652,c_2])).

tff(c_2660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_2656])).

%------------------------------------------------------------------------------
