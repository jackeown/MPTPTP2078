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
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 9.70s
% Output     : CNFRefutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :  166 (5291 expanded)
%              Number of leaves         :   57 (1871 expanded)
%              Depth                    :   31
%              Number of atoms          :  570 (15241 expanded)
%              Number of equality atoms :   27 (4291 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > v1_partfun1 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_4 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( ! [B,C] :
              ( ( r2_hidden(B,A)
                & r2_hidden(C,A) )
             => r2_hidden(k3_xboole_0(B,C),A) )
         => v2_lattice3(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_1)).

tff(f_171,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_163,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_159,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_149,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r2_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_205,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r2_hidden(k3_xboole_0(B,C),A)
               => k11_lattice3(k2_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_179,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_192,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) ) )
                    & ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) )
                     => r1_lattice3(A,k2_tarski(C,D),B) )
                    & ( r2_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) ) )
                    & ( ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) )
                     => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_88,plain,(
    ~ v2_lattice3(k2_yellow_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_76,plain,(
    ! [A_77] : v5_orders_2(k2_yellow_1(A_77)) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_68,plain,(
    ! [A_76] : l1_orders_2(k2_yellow_1(A_76)) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    ! [A_77] : v1_orders_2(k2_yellow_1(A_77)) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_10,plain,(
    ! [A_10] :
      ( g1_orders_2(u1_struct_0(A_10),u1_orders_2(A_10)) = A_10
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_75] : m1_subset_1(k1_yellow_1(A_75),k1_zfmisc_1(k2_zfmisc_1(A_75,A_75))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    ! [A_74] : g1_orders_2(A_74,k1_yellow_1(A_74)) = k2_yellow_1(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_220,plain,(
    ! [C_137,A_138,D_139,B_140] :
      ( C_137 = A_138
      | g1_orders_2(C_137,D_139) != g1_orders_2(A_138,B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_228,plain,(
    ! [C_137,A_74,D_139] :
      ( C_137 = A_74
      | k2_yellow_1(A_74) != g1_orders_2(C_137,D_139)
      | ~ m1_subset_1(k1_yellow_1(A_74),k1_zfmisc_1(k2_zfmisc_1(A_74,A_74))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_220])).

tff(c_231,plain,(
    ! [C_141,A_142,D_143] :
      ( C_141 = A_142
      | k2_yellow_1(A_142) != g1_orders_2(C_141,D_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_228])).

tff(c_234,plain,(
    ! [A_10,A_142] :
      ( u1_struct_0(A_10) = A_142
      | k2_yellow_1(A_142) != A_10
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_231])).

tff(c_251,plain,(
    ! [A_142] :
      ( u1_struct_0(k2_yellow_1(A_142)) = A_142
      | ~ v1_orders_2(k2_yellow_1(A_142))
      | ~ l1_orders_2(k2_yellow_1(A_142)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_234])).

tff(c_255,plain,(
    ! [A_150] : u1_struct_0(k2_yellow_1(A_150)) = A_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_251])).

tff(c_40,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_3'(A_48),u1_struct_0(A_48))
      | v2_lattice3(A_48)
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_264,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_150)),A_150)
      | v2_lattice3(k2_yellow_1(A_150))
      | ~ l1_orders_2(k2_yellow_1(A_150))
      | ~ v5_orders_2(k2_yellow_1(A_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_40])).

tff(c_278,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_150)),A_150)
      | v2_lattice3(k2_yellow_1(A_150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_264])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_38,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_4'(A_48),u1_struct_0(A_48))
      | v2_lattice3(A_48)
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_267,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_4'(k2_yellow_1(A_150)),A_150)
      | v2_lattice3(k2_yellow_1(A_150))
      | ~ l1_orders_2(k2_yellow_1(A_150))
      | ~ v5_orders_2(k2_yellow_1(A_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_38])).

tff(c_280,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_4'(k2_yellow_1(A_150)),A_150)
      | v2_lattice3(k2_yellow_1(A_150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_267])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_253,plain,(
    ! [A_142] : u1_struct_0(k2_yellow_1(A_142)) = A_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_251])).

tff(c_72,plain,(
    ! [A_77] : v3_orders_2(k2_yellow_1(A_77)) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_90,plain,(
    ! [B_95,C_96] :
      ( r2_hidden(k3_xboole_0(B_95,C_96),'#skF_5')
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_86,plain,(
    ! [A_86,B_90,C_92] :
      ( k11_lattice3(k2_yellow_1(A_86),B_90,C_92) = k3_xboole_0(B_90,C_92)
      | ~ r2_hidden(k3_xboole_0(B_90,C_92),A_86)
      | ~ m1_subset_1(C_92,u1_struct_0(k2_yellow_1(A_86)))
      | ~ m1_subset_1(B_90,u1_struct_0(k2_yellow_1(A_86)))
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_612,plain,(
    ! [A_242,B_243,C_244] :
      ( k11_lattice3(k2_yellow_1(A_242),B_243,C_244) = k3_xboole_0(B_243,C_244)
      | ~ r2_hidden(k3_xboole_0(B_243,C_244),A_242)
      | ~ m1_subset_1(C_244,A_242)
      | ~ m1_subset_1(B_243,A_242)
      | v1_xboole_0(A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_86])).

tff(c_625,plain,(
    ! [B_95,C_96] :
      ( k11_lattice3(k2_yellow_1('#skF_5'),B_95,C_96) = k3_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,'#skF_5')
      | ~ m1_subset_1(B_95,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_90,c_612])).

tff(c_629,plain,(
    ! [B_95,C_96] :
      ( k11_lattice3(k2_yellow_1('#skF_5'),B_95,C_96) = k3_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,'#skF_5')
      | ~ m1_subset_1(B_95,'#skF_5')
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_625])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k11_lattice3(A_20,B_21,C_22),u1_struct_0(A_20))
      | ~ m1_subset_1(C_22,u1_struct_0(A_20))
      | ~ m1_subset_1(B_21,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_490,plain,(
    ! [A_210,B_211,C_212] :
      ( r3_orders_2(A_210,B_211,C_212)
      | ~ r1_orders_2(A_210,B_211,C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ m1_subset_1(B_211,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210)
      | ~ v3_orders_2(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_840,plain,(
    ! [A_290,B_291,B_292,C_293] :
      ( r3_orders_2(A_290,B_291,k11_lattice3(A_290,B_292,C_293))
      | ~ r1_orders_2(A_290,B_291,k11_lattice3(A_290,B_292,C_293))
      | ~ m1_subset_1(B_291,u1_struct_0(A_290))
      | ~ v3_orders_2(A_290)
      | v2_struct_0(A_290)
      | ~ m1_subset_1(C_293,u1_struct_0(A_290))
      | ~ m1_subset_1(B_292,u1_struct_0(A_290))
      | ~ l1_orders_2(A_290) ) ),
    inference(resolution,[status(thm)],[c_20,c_490])).

tff(c_849,plain,(
    ! [B_291,B_95,C_96] :
      ( r3_orders_2(k2_yellow_1('#skF_5'),B_291,k3_xboole_0(B_95,C_96))
      | ~ r1_orders_2(k2_yellow_1('#skF_5'),B_291,k11_lattice3(k2_yellow_1('#skF_5'),B_95,C_96))
      | ~ m1_subset_1(B_291,u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ v3_orders_2(k2_yellow_1('#skF_5'))
      | v2_struct_0(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(C_96,u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ m1_subset_1(B_95,u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ l1_orders_2(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(C_96,'#skF_5')
      | ~ m1_subset_1(B_95,'#skF_5')
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_840])).

tff(c_855,plain,(
    ! [B_291,B_95,C_96] :
      ( r3_orders_2(k2_yellow_1('#skF_5'),B_291,k3_xboole_0(B_95,C_96))
      | ~ r1_orders_2(k2_yellow_1('#skF_5'),B_291,k11_lattice3(k2_yellow_1('#skF_5'),B_95,C_96))
      | ~ m1_subset_1(B_291,'#skF_5')
      | v2_struct_0(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(C_96,'#skF_5')
      | ~ m1_subset_1(B_95,'#skF_5')
      | ~ r2_hidden(C_96,'#skF_5')
      | ~ r2_hidden(B_95,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_253,c_253,c_72,c_253,c_849])).

tff(c_891,plain,(
    v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_80,plain,(
    ! [A_78] :
      ( ~ v2_struct_0(k2_yellow_1(A_78))
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_894,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_891,c_80])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_894])).

tff(c_900,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_630,plain,(
    ! [B_245,C_246] :
      ( k11_lattice3(k2_yellow_1('#skF_5'),B_245,C_246) = k3_xboole_0(B_245,C_246)
      | ~ m1_subset_1(C_246,'#skF_5')
      | ~ m1_subset_1(B_245,'#skF_5')
      | ~ r2_hidden(C_246,'#skF_5')
      | ~ r2_hidden(B_245,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_625])).

tff(c_639,plain,(
    ! [B_245,C_246] :
      ( m1_subset_1(k3_xboole_0(B_245,C_246),u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ m1_subset_1(C_246,u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ m1_subset_1(B_245,u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ l1_orders_2(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(C_246,'#skF_5')
      | ~ m1_subset_1(B_245,'#skF_5')
      | ~ r2_hidden(C_246,'#skF_5')
      | ~ r2_hidden(B_245,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_20])).

tff(c_645,plain,(
    ! [B_245,C_246] :
      ( m1_subset_1(k3_xboole_0(B_245,C_246),'#skF_5')
      | ~ m1_subset_1(C_246,'#skF_5')
      | ~ m1_subset_1(B_245,'#skF_5')
      | ~ r2_hidden(C_246,'#skF_5')
      | ~ r2_hidden(B_245,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_253,c_253,c_253,c_639])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [B_112,A_113] : k3_xboole_0(B_112,A_113) = k3_xboole_0(A_113,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [B_112,A_113] : r1_tarski(k3_xboole_0(B_112,A_113),A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_4])).

tff(c_82,plain,(
    ! [A_79,B_83,C_85] :
      ( r3_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | ~ r1_tarski(B_83,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k2_yellow_1(A_79)))
      | ~ m1_subset_1(B_83,u1_struct_0(k2_yellow_1(A_79)))
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_354,plain,(
    ! [A_79,B_83,C_85] :
      ( r3_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | ~ r1_tarski(B_83,C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(B_83,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_82])).

tff(c_483,plain,(
    ! [A_204,B_205,C_206] :
      ( r1_orders_2(A_204,B_205,C_206)
      | ~ r3_orders_2(A_204,B_205,C_206)
      | ~ m1_subset_1(C_206,u1_struct_0(A_204))
      | ~ m1_subset_1(B_205,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ v3_orders_2(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_485,plain,(
    ! [A_79,B_83,C_85] :
      ( r1_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k2_yellow_1(A_79)))
      | ~ m1_subset_1(B_83,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v3_orders_2(k2_yellow_1(A_79))
      | v2_struct_0(k2_yellow_1(A_79))
      | ~ r1_tarski(B_83,C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(B_83,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_354,c_483])).

tff(c_488,plain,(
    ! [A_79,B_83,C_85] :
      ( r1_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | v2_struct_0(k2_yellow_1(A_79))
      | ~ r1_tarski(B_83,C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(B_83,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_253,c_253,c_485])).

tff(c_44,plain,(
    ! [A_59,C_71,D_73,B_67] :
      ( r1_lattice3(A_59,k2_tarski(C_71,D_73),B_67)
      | ~ r1_orders_2(A_59,B_67,D_73)
      | ~ r1_orders_2(A_59,B_67,C_71)
      | ~ m1_subset_1(D_73,u1_struct_0(A_59))
      | ~ m1_subset_1(C_71,u1_struct_0(A_59))
      | ~ m1_subset_1(B_67,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_466,plain,(
    ! [A_198,B_199,C_200] :
      ( m1_subset_1('#skF_1'(A_198,B_199,C_200),u1_struct_0(A_198))
      | r2_yellow_0(A_198,B_199)
      | ~ r1_lattice3(A_198,B_199,C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | ~ v5_orders_2(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_469,plain,(
    ! [A_142,B_199,C_200] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_142),B_199,C_200),A_142)
      | r2_yellow_0(k2_yellow_1(A_142),B_199)
      | ~ r1_lattice3(k2_yellow_1(A_142),B_199,C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(k2_yellow_1(A_142)))
      | ~ l1_orders_2(k2_yellow_1(A_142))
      | ~ v5_orders_2(k2_yellow_1(A_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_466])).

tff(c_471,plain,(
    ! [A_142,B_199,C_200] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_142),B_199,C_200),A_142)
      | r2_yellow_0(k2_yellow_1(A_142),B_199)
      | ~ r1_lattice3(k2_yellow_1(A_142),B_199,C_200)
      | ~ m1_subset_1(C_200,A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_253,c_469])).

tff(c_30,plain,(
    ! [A_23,B_37,C_44] :
      ( r1_lattice3(A_23,B_37,'#skF_1'(A_23,B_37,C_44))
      | r2_yellow_0(A_23,B_37)
      | ~ r1_lattice3(A_23,B_37,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_565,plain,(
    ! [A_222,B_223,D_224,C_225] :
      ( r1_orders_2(A_222,B_223,D_224)
      | ~ r1_lattice3(A_222,k2_tarski(C_225,D_224),B_223)
      | ~ m1_subset_1(D_224,u1_struct_0(A_222))
      | ~ m1_subset_1(C_225,u1_struct_0(A_222))
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1426,plain,(
    ! [A_413,C_414,D_415,C_416] :
      ( r1_orders_2(A_413,'#skF_1'(A_413,k2_tarski(C_414,D_415),C_416),D_415)
      | ~ m1_subset_1(D_415,u1_struct_0(A_413))
      | ~ m1_subset_1(C_414,u1_struct_0(A_413))
      | ~ m1_subset_1('#skF_1'(A_413,k2_tarski(C_414,D_415),C_416),u1_struct_0(A_413))
      | r2_yellow_0(A_413,k2_tarski(C_414,D_415))
      | ~ r1_lattice3(A_413,k2_tarski(C_414,D_415),C_416)
      | ~ m1_subset_1(C_416,u1_struct_0(A_413))
      | ~ l1_orders_2(A_413)
      | ~ v5_orders_2(A_413) ) ),
    inference(resolution,[status(thm)],[c_30,c_565])).

tff(c_1431,plain,(
    ! [A_142,C_414,D_415,C_416] :
      ( r1_orders_2(k2_yellow_1(A_142),'#skF_1'(k2_yellow_1(A_142),k2_tarski(C_414,D_415),C_416),D_415)
      | ~ m1_subset_1(D_415,u1_struct_0(k2_yellow_1(A_142)))
      | ~ m1_subset_1(C_414,u1_struct_0(k2_yellow_1(A_142)))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_142),k2_tarski(C_414,D_415),C_416),A_142)
      | r2_yellow_0(k2_yellow_1(A_142),k2_tarski(C_414,D_415))
      | ~ r1_lattice3(k2_yellow_1(A_142),k2_tarski(C_414,D_415),C_416)
      | ~ m1_subset_1(C_416,u1_struct_0(k2_yellow_1(A_142)))
      | ~ l1_orders_2(k2_yellow_1(A_142))
      | ~ v5_orders_2(k2_yellow_1(A_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_1426])).

tff(c_2673,plain,(
    ! [A_538,C_539,D_540,C_541] :
      ( r1_orders_2(k2_yellow_1(A_538),'#skF_1'(k2_yellow_1(A_538),k2_tarski(C_539,D_540),C_541),D_540)
      | ~ m1_subset_1(D_540,A_538)
      | ~ m1_subset_1(C_539,A_538)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_538),k2_tarski(C_539,D_540),C_541),A_538)
      | r2_yellow_0(k2_yellow_1(A_538),k2_tarski(C_539,D_540))
      | ~ r1_lattice3(k2_yellow_1(A_538),k2_tarski(C_539,D_540),C_541)
      | ~ m1_subset_1(C_541,A_538) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_253,c_253,c_253,c_1431])).

tff(c_511,plain,(
    ! [A_142,B_211,C_212] :
      ( r3_orders_2(k2_yellow_1(A_142),B_211,C_212)
      | ~ r1_orders_2(k2_yellow_1(A_142),B_211,C_212)
      | ~ m1_subset_1(C_212,A_142)
      | ~ m1_subset_1(B_211,u1_struct_0(k2_yellow_1(A_142)))
      | ~ l1_orders_2(k2_yellow_1(A_142))
      | ~ v3_orders_2(k2_yellow_1(A_142))
      | v2_struct_0(k2_yellow_1(A_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_490])).

tff(c_530,plain,(
    ! [A_213,B_214,C_215] :
      ( r3_orders_2(k2_yellow_1(A_213),B_214,C_215)
      | ~ r1_orders_2(k2_yellow_1(A_213),B_214,C_215)
      | ~ m1_subset_1(C_215,A_213)
      | ~ m1_subset_1(B_214,A_213)
      | v2_struct_0(k2_yellow_1(A_213)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_253,c_511])).

tff(c_84,plain,(
    ! [B_83,C_85,A_79] :
      ( r1_tarski(B_83,C_85)
      | ~ r3_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k2_yellow_1(A_79)))
      | ~ m1_subset_1(B_83,u1_struct_0(k2_yellow_1(A_79)))
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_350,plain,(
    ! [B_83,C_85,A_79] :
      ( r1_tarski(B_83,C_85)
      | ~ r3_orders_2(k2_yellow_1(A_79),B_83,C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(B_83,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_84])).

tff(c_539,plain,(
    ! [B_214,C_215,A_213] :
      ( r1_tarski(B_214,C_215)
      | v1_xboole_0(A_213)
      | ~ r1_orders_2(k2_yellow_1(A_213),B_214,C_215)
      | ~ m1_subset_1(C_215,A_213)
      | ~ m1_subset_1(B_214,A_213)
      | v2_struct_0(k2_yellow_1(A_213)) ) ),
    inference(resolution,[status(thm)],[c_530,c_350])).

tff(c_3503,plain,(
    ! [A_684,C_685,D_686,C_687] :
      ( r1_tarski('#skF_1'(k2_yellow_1(A_684),k2_tarski(C_685,D_686),C_687),D_686)
      | v1_xboole_0(A_684)
      | v2_struct_0(k2_yellow_1(A_684))
      | ~ m1_subset_1(D_686,A_684)
      | ~ m1_subset_1(C_685,A_684)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_684),k2_tarski(C_685,D_686),C_687),A_684)
      | r2_yellow_0(k2_yellow_1(A_684),k2_tarski(C_685,D_686))
      | ~ r1_lattice3(k2_yellow_1(A_684),k2_tarski(C_685,D_686),C_687)
      | ~ m1_subset_1(C_687,A_684) ) ),
    inference(resolution,[status(thm)],[c_2673,c_539])).

tff(c_3507,plain,(
    ! [A_142,C_685,D_686,C_200] :
      ( r1_tarski('#skF_1'(k2_yellow_1(A_142),k2_tarski(C_685,D_686),C_200),D_686)
      | v1_xboole_0(A_142)
      | v2_struct_0(k2_yellow_1(A_142))
      | ~ m1_subset_1(D_686,A_142)
      | ~ m1_subset_1(C_685,A_142)
      | r2_yellow_0(k2_yellow_1(A_142),k2_tarski(C_685,D_686))
      | ~ r1_lattice3(k2_yellow_1(A_142),k2_tarski(C_685,D_686),C_200)
      | ~ m1_subset_1(C_200,A_142) ) ),
    inference(resolution,[status(thm)],[c_471,c_3503])).

tff(c_578,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( r1_orders_2(A_234,B_235,C_236)
      | ~ r1_lattice3(A_234,k2_tarski(C_236,D_237),B_235)
      | ~ m1_subset_1(D_237,u1_struct_0(A_234))
      | ~ m1_subset_1(C_236,u1_struct_0(A_234))
      | ~ m1_subset_1(B_235,u1_struct_0(A_234))
      | ~ l1_orders_2(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1304,plain,(
    ! [A_382,C_383,D_384,C_385] :
      ( r1_orders_2(A_382,'#skF_1'(A_382,k2_tarski(C_383,D_384),C_385),C_383)
      | ~ m1_subset_1(D_384,u1_struct_0(A_382))
      | ~ m1_subset_1(C_383,u1_struct_0(A_382))
      | ~ m1_subset_1('#skF_1'(A_382,k2_tarski(C_383,D_384),C_385),u1_struct_0(A_382))
      | r2_yellow_0(A_382,k2_tarski(C_383,D_384))
      | ~ r1_lattice3(A_382,k2_tarski(C_383,D_384),C_385)
      | ~ m1_subset_1(C_385,u1_struct_0(A_382))
      | ~ l1_orders_2(A_382)
      | ~ v5_orders_2(A_382) ) ),
    inference(resolution,[status(thm)],[c_30,c_578])).

tff(c_1309,plain,(
    ! [A_142,C_383,D_384,C_385] :
      ( r1_orders_2(k2_yellow_1(A_142),'#skF_1'(k2_yellow_1(A_142),k2_tarski(C_383,D_384),C_385),C_383)
      | ~ m1_subset_1(D_384,u1_struct_0(k2_yellow_1(A_142)))
      | ~ m1_subset_1(C_383,u1_struct_0(k2_yellow_1(A_142)))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_142),k2_tarski(C_383,D_384),C_385),A_142)
      | r2_yellow_0(k2_yellow_1(A_142),k2_tarski(C_383,D_384))
      | ~ r1_lattice3(k2_yellow_1(A_142),k2_tarski(C_383,D_384),C_385)
      | ~ m1_subset_1(C_385,u1_struct_0(k2_yellow_1(A_142)))
      | ~ l1_orders_2(k2_yellow_1(A_142))
      | ~ v5_orders_2(k2_yellow_1(A_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_1304])).

tff(c_2503,plain,(
    ! [A_516,C_517,D_518,C_519] :
      ( r1_orders_2(k2_yellow_1(A_516),'#skF_1'(k2_yellow_1(A_516),k2_tarski(C_517,D_518),C_519),C_517)
      | ~ m1_subset_1(D_518,A_516)
      | ~ m1_subset_1(C_517,A_516)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_516),k2_tarski(C_517,D_518),C_519),A_516)
      | r2_yellow_0(k2_yellow_1(A_516),k2_tarski(C_517,D_518))
      | ~ r1_lattice3(k2_yellow_1(A_516),k2_tarski(C_517,D_518),C_519)
      | ~ m1_subset_1(C_519,A_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_253,c_253,c_253,c_1309])).

tff(c_3466,plain,(
    ! [A_672,C_673,D_674,C_675] :
      ( r1_tarski('#skF_1'(k2_yellow_1(A_672),k2_tarski(C_673,D_674),C_675),C_673)
      | v1_xboole_0(A_672)
      | v2_struct_0(k2_yellow_1(A_672))
      | ~ m1_subset_1(D_674,A_672)
      | ~ m1_subset_1(C_673,A_672)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_672),k2_tarski(C_673,D_674),C_675),A_672)
      | r2_yellow_0(k2_yellow_1(A_672),k2_tarski(C_673,D_674))
      | ~ r1_lattice3(k2_yellow_1(A_672),k2_tarski(C_673,D_674),C_675)
      | ~ m1_subset_1(C_675,A_672) ) ),
    inference(resolution,[status(thm)],[c_2503,c_539])).

tff(c_3470,plain,(
    ! [A_142,C_673,D_674,C_200] :
      ( r1_tarski('#skF_1'(k2_yellow_1(A_142),k2_tarski(C_673,D_674),C_200),C_673)
      | v1_xboole_0(A_142)
      | v2_struct_0(k2_yellow_1(A_142))
      | ~ m1_subset_1(D_674,A_142)
      | ~ m1_subset_1(C_673,A_142)
      | r2_yellow_0(k2_yellow_1(A_142),k2_tarski(C_673,D_674))
      | ~ r1_lattice3(k2_yellow_1(A_142),k2_tarski(C_673,D_674),C_200)
      | ~ m1_subset_1(C_200,A_142) ) ),
    inference(resolution,[status(thm)],[c_471,c_3466])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_540,plain,(
    ! [A_216,B_217,C_218] :
      ( ~ r1_orders_2(A_216,'#skF_1'(A_216,B_217,C_218),C_218)
      | r2_yellow_0(A_216,B_217)
      | ~ r1_lattice3(A_216,B_217,C_218)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216)
      | ~ v5_orders_2(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_544,plain,(
    ! [A_79,B_217,C_85] :
      ( r2_yellow_0(k2_yellow_1(A_79),B_217)
      | ~ r1_lattice3(k2_yellow_1(A_79),B_217,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79))
      | v2_struct_0(k2_yellow_1(A_79))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_79),B_217,C_85),C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_79),B_217,C_85),A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_488,c_540])).

tff(c_831,plain,(
    ! [A_287,B_288,C_289] :
      ( r2_yellow_0(k2_yellow_1(A_287),B_288)
      | ~ r1_lattice3(k2_yellow_1(A_287),B_288,C_289)
      | v2_struct_0(k2_yellow_1(A_287))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_287),B_288,C_289),C_289)
      | ~ m1_subset_1(C_289,A_287)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_287),B_288,C_289),A_287)
      | v1_xboole_0(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68,c_253,c_544])).

tff(c_4531,plain,(
    ! [A_785,B_786,B_787,C_788] :
      ( r2_yellow_0(k2_yellow_1(A_785),B_786)
      | ~ r1_lattice3(k2_yellow_1(A_785),B_786,k3_xboole_0(B_787,C_788))
      | v2_struct_0(k2_yellow_1(A_785))
      | ~ m1_subset_1(k3_xboole_0(B_787,C_788),A_785)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_785),B_786,k3_xboole_0(B_787,C_788)),A_785)
      | v1_xboole_0(A_785)
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_785),B_786,k3_xboole_0(B_787,C_788)),C_788)
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_785),B_786,k3_xboole_0(B_787,C_788)),B_787) ) ),
    inference(resolution,[status(thm)],[c_6,c_831])).

tff(c_4540,plain,(
    ! [A_789,B_790,B_791,C_792] :
      ( v2_struct_0(k2_yellow_1(A_789))
      | v1_xboole_0(A_789)
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_789),B_790,k3_xboole_0(B_791,C_792)),C_792)
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_789),B_790,k3_xboole_0(B_791,C_792)),B_791)
      | r2_yellow_0(k2_yellow_1(A_789),B_790)
      | ~ r1_lattice3(k2_yellow_1(A_789),B_790,k3_xboole_0(B_791,C_792))
      | ~ m1_subset_1(k3_xboole_0(B_791,C_792),A_789) ) ),
    inference(resolution,[status(thm)],[c_471,c_4531])).

tff(c_4615,plain,(
    ! [A_800,C_801,D_802,B_803] :
      ( ~ r1_tarski('#skF_1'(k2_yellow_1(A_800),k2_tarski(C_801,D_802),k3_xboole_0(B_803,C_801)),B_803)
      | v1_xboole_0(A_800)
      | v2_struct_0(k2_yellow_1(A_800))
      | ~ m1_subset_1(D_802,A_800)
      | ~ m1_subset_1(C_801,A_800)
      | r2_yellow_0(k2_yellow_1(A_800),k2_tarski(C_801,D_802))
      | ~ r1_lattice3(k2_yellow_1(A_800),k2_tarski(C_801,D_802),k3_xboole_0(B_803,C_801))
      | ~ m1_subset_1(k3_xboole_0(B_803,C_801),A_800) ) ),
    inference(resolution,[status(thm)],[c_3470,c_4540])).

tff(c_4642,plain,(
    ! [A_804,D_805,C_806] :
      ( v1_xboole_0(A_804)
      | v2_struct_0(k2_yellow_1(A_804))
      | ~ m1_subset_1(D_805,A_804)
      | ~ m1_subset_1(C_806,A_804)
      | r2_yellow_0(k2_yellow_1(A_804),k2_tarski(C_806,D_805))
      | ~ r1_lattice3(k2_yellow_1(A_804),k2_tarski(C_806,D_805),k3_xboole_0(D_805,C_806))
      | ~ m1_subset_1(k3_xboole_0(D_805,C_806),A_804) ) ),
    inference(resolution,[status(thm)],[c_3507,c_4615])).

tff(c_4646,plain,(
    ! [A_804,D_73,C_71] :
      ( v1_xboole_0(A_804)
      | v2_struct_0(k2_yellow_1(A_804))
      | ~ m1_subset_1(D_73,A_804)
      | ~ m1_subset_1(C_71,A_804)
      | r2_yellow_0(k2_yellow_1(A_804),k2_tarski(C_71,D_73))
      | ~ m1_subset_1(k3_xboole_0(D_73,C_71),A_804)
      | ~ r1_orders_2(k2_yellow_1(A_804),k3_xboole_0(D_73,C_71),D_73)
      | ~ r1_orders_2(k2_yellow_1(A_804),k3_xboole_0(D_73,C_71),C_71)
      | ~ m1_subset_1(D_73,u1_struct_0(k2_yellow_1(A_804)))
      | ~ m1_subset_1(C_71,u1_struct_0(k2_yellow_1(A_804)))
      | ~ m1_subset_1(k3_xboole_0(D_73,C_71),u1_struct_0(k2_yellow_1(A_804)))
      | ~ l1_orders_2(k2_yellow_1(A_804)) ) ),
    inference(resolution,[status(thm)],[c_44,c_4642])).

tff(c_4973,plain,(
    ! [A_827,C_828,D_829] :
      ( v1_xboole_0(A_827)
      | v2_struct_0(k2_yellow_1(A_827))
      | r2_yellow_0(k2_yellow_1(A_827),k2_tarski(C_828,D_829))
      | ~ r1_orders_2(k2_yellow_1(A_827),k3_xboole_0(D_829,C_828),D_829)
      | ~ r1_orders_2(k2_yellow_1(A_827),k3_xboole_0(D_829,C_828),C_828)
      | ~ m1_subset_1(D_829,A_827)
      | ~ m1_subset_1(C_828,A_827)
      | ~ m1_subset_1(k3_xboole_0(D_829,C_828),A_827) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_253,c_253,c_253,c_4646])).

tff(c_4994,plain,(
    ! [A_79,C_828,C_85] :
      ( r2_yellow_0(k2_yellow_1(A_79),k2_tarski(C_828,C_85))
      | ~ r1_orders_2(k2_yellow_1(A_79),k3_xboole_0(C_85,C_828),C_828)
      | ~ m1_subset_1(C_828,A_79)
      | v2_struct_0(k2_yellow_1(A_79))
      | ~ r1_tarski(k3_xboole_0(C_85,C_828),C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(k3_xboole_0(C_85,C_828),A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_488,c_4973])).

tff(c_5028,plain,(
    ! [A_833,C_834,C_835] :
      ( r2_yellow_0(k2_yellow_1(A_833),k2_tarski(C_834,C_835))
      | ~ r1_orders_2(k2_yellow_1(A_833),k3_xboole_0(C_835,C_834),C_834)
      | ~ m1_subset_1(C_834,A_833)
      | v2_struct_0(k2_yellow_1(A_833))
      | ~ m1_subset_1(C_835,A_833)
      | ~ m1_subset_1(k3_xboole_0(C_835,C_834),A_833)
      | v1_xboole_0(A_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4994])).

tff(c_5056,plain,(
    ! [A_79,C_85,C_835] :
      ( r2_yellow_0(k2_yellow_1(A_79),k2_tarski(C_85,C_835))
      | ~ m1_subset_1(C_835,A_79)
      | v2_struct_0(k2_yellow_1(A_79))
      | ~ r1_tarski(k3_xboole_0(C_835,C_85),C_85)
      | ~ m1_subset_1(C_85,A_79)
      | ~ m1_subset_1(k3_xboole_0(C_835,C_85),A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_488,c_5028])).

tff(c_5092,plain,(
    ! [A_836,C_837,C_838] :
      ( r2_yellow_0(k2_yellow_1(A_836),k2_tarski(C_837,C_838))
      | ~ m1_subset_1(C_838,A_836)
      | v2_struct_0(k2_yellow_1(A_836))
      | ~ m1_subset_1(C_837,A_836)
      | ~ m1_subset_1(k3_xboole_0(C_838,C_837),A_836)
      | v1_xboole_0(A_836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_5056])).

tff(c_36,plain,(
    ! [A_48] :
      ( ~ r2_yellow_0(A_48,k2_tarski('#skF_3'(A_48),'#skF_4'(A_48)))
      | v2_lattice3(A_48)
      | ~ l1_orders_2(A_48)
      | ~ v5_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5100,plain,(
    ! [A_836] :
      ( v2_lattice3(k2_yellow_1(A_836))
      | ~ l1_orders_2(k2_yellow_1(A_836))
      | ~ v5_orders_2(k2_yellow_1(A_836))
      | ~ m1_subset_1('#skF_4'(k2_yellow_1(A_836)),A_836)
      | v2_struct_0(k2_yellow_1(A_836))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_836)),A_836)
      | ~ m1_subset_1(k3_xboole_0('#skF_4'(k2_yellow_1(A_836)),'#skF_3'(k2_yellow_1(A_836))),A_836)
      | v1_xboole_0(A_836) ) ),
    inference(resolution,[status(thm)],[c_5092,c_36])).

tff(c_5139,plain,(
    ! [A_845] :
      ( v2_lattice3(k2_yellow_1(A_845))
      | ~ m1_subset_1('#skF_4'(k2_yellow_1(A_845)),A_845)
      | v2_struct_0(k2_yellow_1(A_845))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_845)),A_845)
      | ~ m1_subset_1(k3_xboole_0('#skF_3'(k2_yellow_1(A_845)),'#skF_4'(k2_yellow_1(A_845))),A_845)
      | v1_xboole_0(A_845) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76,c_68,c_5100])).

tff(c_5143,plain,
    ( v2_lattice3(k2_yellow_1('#skF_5'))
    | v2_struct_0(k2_yellow_1('#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_645,c_5139])).

tff(c_5146,plain,
    ( ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_900,c_88,c_5143])).

tff(c_5147,plain,(
    ~ r2_hidden('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5146])).

tff(c_5150,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_5147])).

tff(c_5153,plain,(
    ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5150])).

tff(c_5156,plain,(
    v2_lattice3(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_278,c_5153])).

tff(c_5160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5156])).

tff(c_5161,plain,
    ( ~ r2_hidden('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5146])).

tff(c_5164,plain,(
    ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5161])).

tff(c_5167,plain,(
    v2_lattice3(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_280,c_5164])).

tff(c_5171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5167])).

tff(c_5173,plain,(
    m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5161])).

tff(c_5172,plain,
    ( ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5161])).

tff(c_5323,plain,(
    ~ r2_hidden('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5172])).

tff(c_5326,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_5323])).

tff(c_5329,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_5326])).

tff(c_5331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5329])).

tff(c_5332,plain,(
    ~ m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5172])).

tff(c_5336,plain,(
    v2_lattice3(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_278,c_5332])).

tff(c_5340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.70/3.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.70/3.42  
% 9.70/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.70/3.43  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > v1_partfun1 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_4 > #skF_5 > #skF_3 > #skF_2
% 9.70/3.43  
% 9.70/3.43  %Foreground sorts:
% 9.70/3.43  
% 9.70/3.43  
% 9.70/3.43  %Background operators:
% 9.70/3.43  
% 9.70/3.43  
% 9.70/3.43  %Foreground operators:
% 9.70/3.43  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 9.70/3.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.70/3.43  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 9.70/3.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.70/3.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.70/3.43  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.70/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.70/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.70/3.43  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.70/3.43  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 9.70/3.43  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 9.70/3.43  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 9.70/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.70/3.43  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 9.70/3.43  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 9.70/3.43  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 9.70/3.43  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 9.70/3.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.70/3.43  tff('#skF_5', type, '#skF_5': $i).
% 9.70/3.43  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 9.70/3.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.70/3.43  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 9.70/3.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.70/3.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.70/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.70/3.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.70/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.70/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.70/3.43  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 9.70/3.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.70/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.70/3.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.70/3.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.70/3.43  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 9.70/3.43  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 9.70/3.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.70/3.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.70/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.70/3.43  
% 9.92/3.45  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => ((![B, C]: ((r2_hidden(B, A) & r2_hidden(C, A)) => r2_hidden(k3_xboole_0(B, C), A))) => v2_lattice3(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_1)).
% 9.92/3.45  tff(f_171, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 9.92/3.45  tff(f_163, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 9.92/3.45  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 9.92/3.45  tff(f_159, axiom, (![A]: ((((v1_relat_2(k1_yellow_1(A)) & v4_relat_2(k1_yellow_1(A))) & v8_relat_2(k1_yellow_1(A))) & v1_partfun1(k1_yellow_1(A), A)) & m1_subset_1(k1_yellow_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 9.92/3.45  tff(f_149, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 9.92/3.45  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 9.92/3.45  tff(f_112, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (v2_lattice3(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r2_yellow_0(A, k2_tarski(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_0)).
% 9.92/3.45  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 9.92/3.45  tff(f_205, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k3_xboole_0(B, C), A) => (k11_lattice3(k2_yellow_1(A), B, C) = k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_1)).
% 9.92/3.45  tff(f_79, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 9.92/3.45  tff(f_71, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.92/3.45  tff(f_179, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 9.92/3.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.92/3.45  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.92/3.45  tff(f_192, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 9.92/3.45  tff(f_147, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((r1_lattice3(A, k2_tarski(C, D), B) => (r1_orders_2(A, B, C) & r1_orders_2(A, B, D))) & ((r1_orders_2(A, B, C) & r1_orders_2(A, B, D)) => r1_lattice3(A, k2_tarski(C, D), B))) & (r2_lattice3(A, k2_tarski(C, D), B) => (r1_orders_2(A, C, B) & r1_orders_2(A, D, B)))) & ((r1_orders_2(A, C, B) & r1_orders_2(A, D, B)) => r2_lattice3(A, k2_tarski(C, D), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_0)).
% 9.92/3.45  tff(f_98, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (r2_yellow_0(A, B) <=> (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r1_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_yellow_0)).
% 9.92/3.45  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.92/3.45  tff(c_88, plain, (~v2_lattice3(k2_yellow_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.92/3.45  tff(c_76, plain, (![A_77]: (v5_orders_2(k2_yellow_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.92/3.45  tff(c_68, plain, (![A_76]: (l1_orders_2(k2_yellow_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.92/3.45  tff(c_70, plain, (![A_77]: (v1_orders_2(k2_yellow_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.92/3.45  tff(c_10, plain, (![A_10]: (g1_orders_2(u1_struct_0(A_10), u1_orders_2(A_10))=A_10 | ~v1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.92/3.45  tff(c_64, plain, (![A_75]: (m1_subset_1(k1_yellow_1(A_75), k1_zfmisc_1(k2_zfmisc_1(A_75, A_75))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 9.92/3.45  tff(c_54, plain, (![A_74]: (g1_orders_2(A_74, k1_yellow_1(A_74))=k2_yellow_1(A_74))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.92/3.45  tff(c_220, plain, (![C_137, A_138, D_139, B_140]: (C_137=A_138 | g1_orders_2(C_137, D_139)!=g1_orders_2(A_138, B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.92/3.45  tff(c_228, plain, (![C_137, A_74, D_139]: (C_137=A_74 | k2_yellow_1(A_74)!=g1_orders_2(C_137, D_139) | ~m1_subset_1(k1_yellow_1(A_74), k1_zfmisc_1(k2_zfmisc_1(A_74, A_74))))), inference(superposition, [status(thm), theory('equality')], [c_54, c_220])).
% 9.92/3.45  tff(c_231, plain, (![C_141, A_142, D_143]: (C_141=A_142 | k2_yellow_1(A_142)!=g1_orders_2(C_141, D_143))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_228])).
% 9.92/3.45  tff(c_234, plain, (![A_10, A_142]: (u1_struct_0(A_10)=A_142 | k2_yellow_1(A_142)!=A_10 | ~v1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_231])).
% 9.92/3.45  tff(c_251, plain, (![A_142]: (u1_struct_0(k2_yellow_1(A_142))=A_142 | ~v1_orders_2(k2_yellow_1(A_142)) | ~l1_orders_2(k2_yellow_1(A_142)))), inference(reflexivity, [status(thm), theory('equality')], [c_234])).
% 9.92/3.45  tff(c_255, plain, (![A_150]: (u1_struct_0(k2_yellow_1(A_150))=A_150)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_251])).
% 9.92/3.45  tff(c_40, plain, (![A_48]: (m1_subset_1('#skF_3'(A_48), u1_struct_0(A_48)) | v2_lattice3(A_48) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.92/3.45  tff(c_264, plain, (![A_150]: (m1_subset_1('#skF_3'(k2_yellow_1(A_150)), A_150) | v2_lattice3(k2_yellow_1(A_150)) | ~l1_orders_2(k2_yellow_1(A_150)) | ~v5_orders_2(k2_yellow_1(A_150)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_40])).
% 9.92/3.45  tff(c_278, plain, (![A_150]: (m1_subset_1('#skF_3'(k2_yellow_1(A_150)), A_150) | v2_lattice3(k2_yellow_1(A_150)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_264])).
% 9.92/3.45  tff(c_92, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.92/3.45  tff(c_38, plain, (![A_48]: (m1_subset_1('#skF_4'(A_48), u1_struct_0(A_48)) | v2_lattice3(A_48) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.92/3.45  tff(c_267, plain, (![A_150]: (m1_subset_1('#skF_4'(k2_yellow_1(A_150)), A_150) | v2_lattice3(k2_yellow_1(A_150)) | ~l1_orders_2(k2_yellow_1(A_150)) | ~v5_orders_2(k2_yellow_1(A_150)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_38])).
% 9.92/3.45  tff(c_280, plain, (![A_150]: (m1_subset_1('#skF_4'(k2_yellow_1(A_150)), A_150) | v2_lattice3(k2_yellow_1(A_150)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_267])).
% 9.92/3.46  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.92/3.46  tff(c_253, plain, (![A_142]: (u1_struct_0(k2_yellow_1(A_142))=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_251])).
% 9.92/3.46  tff(c_72, plain, (![A_77]: (v3_orders_2(k2_yellow_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_171])).
% 9.92/3.46  tff(c_90, plain, (![B_95, C_96]: (r2_hidden(k3_xboole_0(B_95, C_96), '#skF_5') | ~r2_hidden(C_96, '#skF_5') | ~r2_hidden(B_95, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.92/3.46  tff(c_86, plain, (![A_86, B_90, C_92]: (k11_lattice3(k2_yellow_1(A_86), B_90, C_92)=k3_xboole_0(B_90, C_92) | ~r2_hidden(k3_xboole_0(B_90, C_92), A_86) | ~m1_subset_1(C_92, u1_struct_0(k2_yellow_1(A_86))) | ~m1_subset_1(B_90, u1_struct_0(k2_yellow_1(A_86))) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.92/3.46  tff(c_612, plain, (![A_242, B_243, C_244]: (k11_lattice3(k2_yellow_1(A_242), B_243, C_244)=k3_xboole_0(B_243, C_244) | ~r2_hidden(k3_xboole_0(B_243, C_244), A_242) | ~m1_subset_1(C_244, A_242) | ~m1_subset_1(B_243, A_242) | v1_xboole_0(A_242))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_86])).
% 9.92/3.46  tff(c_625, plain, (![B_95, C_96]: (k11_lattice3(k2_yellow_1('#skF_5'), B_95, C_96)=k3_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, '#skF_5') | ~m1_subset_1(B_95, '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden(C_96, '#skF_5') | ~r2_hidden(B_95, '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_612])).
% 9.92/3.46  tff(c_629, plain, (![B_95, C_96]: (k11_lattice3(k2_yellow_1('#skF_5'), B_95, C_96)=k3_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, '#skF_5') | ~m1_subset_1(B_95, '#skF_5') | ~r2_hidden(C_96, '#skF_5') | ~r2_hidden(B_95, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_625])).
% 9.92/3.46  tff(c_20, plain, (![A_20, B_21, C_22]: (m1_subset_1(k11_lattice3(A_20, B_21, C_22), u1_struct_0(A_20)) | ~m1_subset_1(C_22, u1_struct_0(A_20)) | ~m1_subset_1(B_21, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.92/3.46  tff(c_490, plain, (![A_210, B_211, C_212]: (r3_orders_2(A_210, B_211, C_212) | ~r1_orders_2(A_210, B_211, C_212) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~m1_subset_1(B_211, u1_struct_0(A_210)) | ~l1_orders_2(A_210) | ~v3_orders_2(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.92/3.46  tff(c_840, plain, (![A_290, B_291, B_292, C_293]: (r3_orders_2(A_290, B_291, k11_lattice3(A_290, B_292, C_293)) | ~r1_orders_2(A_290, B_291, k11_lattice3(A_290, B_292, C_293)) | ~m1_subset_1(B_291, u1_struct_0(A_290)) | ~v3_orders_2(A_290) | v2_struct_0(A_290) | ~m1_subset_1(C_293, u1_struct_0(A_290)) | ~m1_subset_1(B_292, u1_struct_0(A_290)) | ~l1_orders_2(A_290))), inference(resolution, [status(thm)], [c_20, c_490])).
% 9.92/3.46  tff(c_849, plain, (![B_291, B_95, C_96]: (r3_orders_2(k2_yellow_1('#skF_5'), B_291, k3_xboole_0(B_95, C_96)) | ~r1_orders_2(k2_yellow_1('#skF_5'), B_291, k11_lattice3(k2_yellow_1('#skF_5'), B_95, C_96)) | ~m1_subset_1(B_291, u1_struct_0(k2_yellow_1('#skF_5'))) | ~v3_orders_2(k2_yellow_1('#skF_5')) | v2_struct_0(k2_yellow_1('#skF_5')) | ~m1_subset_1(C_96, u1_struct_0(k2_yellow_1('#skF_5'))) | ~m1_subset_1(B_95, u1_struct_0(k2_yellow_1('#skF_5'))) | ~l1_orders_2(k2_yellow_1('#skF_5')) | ~m1_subset_1(C_96, '#skF_5') | ~m1_subset_1(B_95, '#skF_5') | ~r2_hidden(C_96, '#skF_5') | ~r2_hidden(B_95, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_629, c_840])).
% 9.92/3.46  tff(c_855, plain, (![B_291, B_95, C_96]: (r3_orders_2(k2_yellow_1('#skF_5'), B_291, k3_xboole_0(B_95, C_96)) | ~r1_orders_2(k2_yellow_1('#skF_5'), B_291, k11_lattice3(k2_yellow_1('#skF_5'), B_95, C_96)) | ~m1_subset_1(B_291, '#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | ~m1_subset_1(C_96, '#skF_5') | ~m1_subset_1(B_95, '#skF_5') | ~r2_hidden(C_96, '#skF_5') | ~r2_hidden(B_95, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_253, c_253, c_72, c_253, c_849])).
% 9.92/3.46  tff(c_891, plain, (v2_struct_0(k2_yellow_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_855])).
% 9.92/3.46  tff(c_80, plain, (![A_78]: (~v2_struct_0(k2_yellow_1(A_78)) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.92/3.46  tff(c_894, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_891, c_80])).
% 9.92/3.46  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_894])).
% 9.92/3.46  tff(c_900, plain, (~v2_struct_0(k2_yellow_1('#skF_5'))), inference(splitRight, [status(thm)], [c_855])).
% 9.92/3.46  tff(c_630, plain, (![B_245, C_246]: (k11_lattice3(k2_yellow_1('#skF_5'), B_245, C_246)=k3_xboole_0(B_245, C_246) | ~m1_subset_1(C_246, '#skF_5') | ~m1_subset_1(B_245, '#skF_5') | ~r2_hidden(C_246, '#skF_5') | ~r2_hidden(B_245, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_625])).
% 9.92/3.46  tff(c_639, plain, (![B_245, C_246]: (m1_subset_1(k3_xboole_0(B_245, C_246), u1_struct_0(k2_yellow_1('#skF_5'))) | ~m1_subset_1(C_246, u1_struct_0(k2_yellow_1('#skF_5'))) | ~m1_subset_1(B_245, u1_struct_0(k2_yellow_1('#skF_5'))) | ~l1_orders_2(k2_yellow_1('#skF_5')) | ~m1_subset_1(C_246, '#skF_5') | ~m1_subset_1(B_245, '#skF_5') | ~r2_hidden(C_246, '#skF_5') | ~r2_hidden(B_245, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_630, c_20])).
% 9.92/3.46  tff(c_645, plain, (![B_245, C_246]: (m1_subset_1(k3_xboole_0(B_245, C_246), '#skF_5') | ~m1_subset_1(C_246, '#skF_5') | ~m1_subset_1(B_245, '#skF_5') | ~r2_hidden(C_246, '#skF_5') | ~r2_hidden(B_245, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_253, c_253, c_253, c_639])).
% 9.92/3.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.92/3.46  tff(c_116, plain, (![B_112, A_113]: (k3_xboole_0(B_112, A_113)=k3_xboole_0(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.92/3.46  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.92/3.46  tff(c_131, plain, (![B_112, A_113]: (r1_tarski(k3_xboole_0(B_112, A_113), A_113))), inference(superposition, [status(thm), theory('equality')], [c_116, c_4])).
% 9.92/3.46  tff(c_82, plain, (![A_79, B_83, C_85]: (r3_orders_2(k2_yellow_1(A_79), B_83, C_85) | ~r1_tarski(B_83, C_85) | ~m1_subset_1(C_85, u1_struct_0(k2_yellow_1(A_79))) | ~m1_subset_1(B_83, u1_struct_0(k2_yellow_1(A_79))) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.92/3.46  tff(c_354, plain, (![A_79, B_83, C_85]: (r3_orders_2(k2_yellow_1(A_79), B_83, C_85) | ~r1_tarski(B_83, C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(B_83, A_79) | v1_xboole_0(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_82])).
% 9.92/3.46  tff(c_483, plain, (![A_204, B_205, C_206]: (r1_orders_2(A_204, B_205, C_206) | ~r3_orders_2(A_204, B_205, C_206) | ~m1_subset_1(C_206, u1_struct_0(A_204)) | ~m1_subset_1(B_205, u1_struct_0(A_204)) | ~l1_orders_2(A_204) | ~v3_orders_2(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.92/3.46  tff(c_485, plain, (![A_79, B_83, C_85]: (r1_orders_2(k2_yellow_1(A_79), B_83, C_85) | ~m1_subset_1(C_85, u1_struct_0(k2_yellow_1(A_79))) | ~m1_subset_1(B_83, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v3_orders_2(k2_yellow_1(A_79)) | v2_struct_0(k2_yellow_1(A_79)) | ~r1_tarski(B_83, C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(B_83, A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_354, c_483])).
% 9.92/3.46  tff(c_488, plain, (![A_79, B_83, C_85]: (r1_orders_2(k2_yellow_1(A_79), B_83, C_85) | v2_struct_0(k2_yellow_1(A_79)) | ~r1_tarski(B_83, C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(B_83, A_79) | v1_xboole_0(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_253, c_253, c_485])).
% 9.92/3.46  tff(c_44, plain, (![A_59, C_71, D_73, B_67]: (r1_lattice3(A_59, k2_tarski(C_71, D_73), B_67) | ~r1_orders_2(A_59, B_67, D_73) | ~r1_orders_2(A_59, B_67, C_71) | ~m1_subset_1(D_73, u1_struct_0(A_59)) | ~m1_subset_1(C_71, u1_struct_0(A_59)) | ~m1_subset_1(B_67, u1_struct_0(A_59)) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.92/3.46  tff(c_466, plain, (![A_198, B_199, C_200]: (m1_subset_1('#skF_1'(A_198, B_199, C_200), u1_struct_0(A_198)) | r2_yellow_0(A_198, B_199) | ~r1_lattice3(A_198, B_199, C_200) | ~m1_subset_1(C_200, u1_struct_0(A_198)) | ~l1_orders_2(A_198) | ~v5_orders_2(A_198))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.92/3.46  tff(c_469, plain, (![A_142, B_199, C_200]: (m1_subset_1('#skF_1'(k2_yellow_1(A_142), B_199, C_200), A_142) | r2_yellow_0(k2_yellow_1(A_142), B_199) | ~r1_lattice3(k2_yellow_1(A_142), B_199, C_200) | ~m1_subset_1(C_200, u1_struct_0(k2_yellow_1(A_142))) | ~l1_orders_2(k2_yellow_1(A_142)) | ~v5_orders_2(k2_yellow_1(A_142)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_466])).
% 9.92/3.46  tff(c_471, plain, (![A_142, B_199, C_200]: (m1_subset_1('#skF_1'(k2_yellow_1(A_142), B_199, C_200), A_142) | r2_yellow_0(k2_yellow_1(A_142), B_199) | ~r1_lattice3(k2_yellow_1(A_142), B_199, C_200) | ~m1_subset_1(C_200, A_142))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_253, c_469])).
% 9.92/3.46  tff(c_30, plain, (![A_23, B_37, C_44]: (r1_lattice3(A_23, B_37, '#skF_1'(A_23, B_37, C_44)) | r2_yellow_0(A_23, B_37) | ~r1_lattice3(A_23, B_37, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.92/3.46  tff(c_565, plain, (![A_222, B_223, D_224, C_225]: (r1_orders_2(A_222, B_223, D_224) | ~r1_lattice3(A_222, k2_tarski(C_225, D_224), B_223) | ~m1_subset_1(D_224, u1_struct_0(A_222)) | ~m1_subset_1(C_225, u1_struct_0(A_222)) | ~m1_subset_1(B_223, u1_struct_0(A_222)) | ~l1_orders_2(A_222))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.92/3.46  tff(c_1426, plain, (![A_413, C_414, D_415, C_416]: (r1_orders_2(A_413, '#skF_1'(A_413, k2_tarski(C_414, D_415), C_416), D_415) | ~m1_subset_1(D_415, u1_struct_0(A_413)) | ~m1_subset_1(C_414, u1_struct_0(A_413)) | ~m1_subset_1('#skF_1'(A_413, k2_tarski(C_414, D_415), C_416), u1_struct_0(A_413)) | r2_yellow_0(A_413, k2_tarski(C_414, D_415)) | ~r1_lattice3(A_413, k2_tarski(C_414, D_415), C_416) | ~m1_subset_1(C_416, u1_struct_0(A_413)) | ~l1_orders_2(A_413) | ~v5_orders_2(A_413))), inference(resolution, [status(thm)], [c_30, c_565])).
% 9.92/3.46  tff(c_1431, plain, (![A_142, C_414, D_415, C_416]: (r1_orders_2(k2_yellow_1(A_142), '#skF_1'(k2_yellow_1(A_142), k2_tarski(C_414, D_415), C_416), D_415) | ~m1_subset_1(D_415, u1_struct_0(k2_yellow_1(A_142))) | ~m1_subset_1(C_414, u1_struct_0(k2_yellow_1(A_142))) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_142), k2_tarski(C_414, D_415), C_416), A_142) | r2_yellow_0(k2_yellow_1(A_142), k2_tarski(C_414, D_415)) | ~r1_lattice3(k2_yellow_1(A_142), k2_tarski(C_414, D_415), C_416) | ~m1_subset_1(C_416, u1_struct_0(k2_yellow_1(A_142))) | ~l1_orders_2(k2_yellow_1(A_142)) | ~v5_orders_2(k2_yellow_1(A_142)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_1426])).
% 9.92/3.46  tff(c_2673, plain, (![A_538, C_539, D_540, C_541]: (r1_orders_2(k2_yellow_1(A_538), '#skF_1'(k2_yellow_1(A_538), k2_tarski(C_539, D_540), C_541), D_540) | ~m1_subset_1(D_540, A_538) | ~m1_subset_1(C_539, A_538) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_538), k2_tarski(C_539, D_540), C_541), A_538) | r2_yellow_0(k2_yellow_1(A_538), k2_tarski(C_539, D_540)) | ~r1_lattice3(k2_yellow_1(A_538), k2_tarski(C_539, D_540), C_541) | ~m1_subset_1(C_541, A_538))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_253, c_253, c_253, c_1431])).
% 9.92/3.46  tff(c_511, plain, (![A_142, B_211, C_212]: (r3_orders_2(k2_yellow_1(A_142), B_211, C_212) | ~r1_orders_2(k2_yellow_1(A_142), B_211, C_212) | ~m1_subset_1(C_212, A_142) | ~m1_subset_1(B_211, u1_struct_0(k2_yellow_1(A_142))) | ~l1_orders_2(k2_yellow_1(A_142)) | ~v3_orders_2(k2_yellow_1(A_142)) | v2_struct_0(k2_yellow_1(A_142)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_490])).
% 9.92/3.46  tff(c_530, plain, (![A_213, B_214, C_215]: (r3_orders_2(k2_yellow_1(A_213), B_214, C_215) | ~r1_orders_2(k2_yellow_1(A_213), B_214, C_215) | ~m1_subset_1(C_215, A_213) | ~m1_subset_1(B_214, A_213) | v2_struct_0(k2_yellow_1(A_213)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_253, c_511])).
% 9.92/3.46  tff(c_84, plain, (![B_83, C_85, A_79]: (r1_tarski(B_83, C_85) | ~r3_orders_2(k2_yellow_1(A_79), B_83, C_85) | ~m1_subset_1(C_85, u1_struct_0(k2_yellow_1(A_79))) | ~m1_subset_1(B_83, u1_struct_0(k2_yellow_1(A_79))) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.92/3.46  tff(c_350, plain, (![B_83, C_85, A_79]: (r1_tarski(B_83, C_85) | ~r3_orders_2(k2_yellow_1(A_79), B_83, C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(B_83, A_79) | v1_xboole_0(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_84])).
% 9.92/3.46  tff(c_539, plain, (![B_214, C_215, A_213]: (r1_tarski(B_214, C_215) | v1_xboole_0(A_213) | ~r1_orders_2(k2_yellow_1(A_213), B_214, C_215) | ~m1_subset_1(C_215, A_213) | ~m1_subset_1(B_214, A_213) | v2_struct_0(k2_yellow_1(A_213)))), inference(resolution, [status(thm)], [c_530, c_350])).
% 9.92/3.46  tff(c_3503, plain, (![A_684, C_685, D_686, C_687]: (r1_tarski('#skF_1'(k2_yellow_1(A_684), k2_tarski(C_685, D_686), C_687), D_686) | v1_xboole_0(A_684) | v2_struct_0(k2_yellow_1(A_684)) | ~m1_subset_1(D_686, A_684) | ~m1_subset_1(C_685, A_684) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_684), k2_tarski(C_685, D_686), C_687), A_684) | r2_yellow_0(k2_yellow_1(A_684), k2_tarski(C_685, D_686)) | ~r1_lattice3(k2_yellow_1(A_684), k2_tarski(C_685, D_686), C_687) | ~m1_subset_1(C_687, A_684))), inference(resolution, [status(thm)], [c_2673, c_539])).
% 9.92/3.46  tff(c_3507, plain, (![A_142, C_685, D_686, C_200]: (r1_tarski('#skF_1'(k2_yellow_1(A_142), k2_tarski(C_685, D_686), C_200), D_686) | v1_xboole_0(A_142) | v2_struct_0(k2_yellow_1(A_142)) | ~m1_subset_1(D_686, A_142) | ~m1_subset_1(C_685, A_142) | r2_yellow_0(k2_yellow_1(A_142), k2_tarski(C_685, D_686)) | ~r1_lattice3(k2_yellow_1(A_142), k2_tarski(C_685, D_686), C_200) | ~m1_subset_1(C_200, A_142))), inference(resolution, [status(thm)], [c_471, c_3503])).
% 9.92/3.46  tff(c_578, plain, (![A_234, B_235, C_236, D_237]: (r1_orders_2(A_234, B_235, C_236) | ~r1_lattice3(A_234, k2_tarski(C_236, D_237), B_235) | ~m1_subset_1(D_237, u1_struct_0(A_234)) | ~m1_subset_1(C_236, u1_struct_0(A_234)) | ~m1_subset_1(B_235, u1_struct_0(A_234)) | ~l1_orders_2(A_234))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.92/3.46  tff(c_1304, plain, (![A_382, C_383, D_384, C_385]: (r1_orders_2(A_382, '#skF_1'(A_382, k2_tarski(C_383, D_384), C_385), C_383) | ~m1_subset_1(D_384, u1_struct_0(A_382)) | ~m1_subset_1(C_383, u1_struct_0(A_382)) | ~m1_subset_1('#skF_1'(A_382, k2_tarski(C_383, D_384), C_385), u1_struct_0(A_382)) | r2_yellow_0(A_382, k2_tarski(C_383, D_384)) | ~r1_lattice3(A_382, k2_tarski(C_383, D_384), C_385) | ~m1_subset_1(C_385, u1_struct_0(A_382)) | ~l1_orders_2(A_382) | ~v5_orders_2(A_382))), inference(resolution, [status(thm)], [c_30, c_578])).
% 9.92/3.46  tff(c_1309, plain, (![A_142, C_383, D_384, C_385]: (r1_orders_2(k2_yellow_1(A_142), '#skF_1'(k2_yellow_1(A_142), k2_tarski(C_383, D_384), C_385), C_383) | ~m1_subset_1(D_384, u1_struct_0(k2_yellow_1(A_142))) | ~m1_subset_1(C_383, u1_struct_0(k2_yellow_1(A_142))) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_142), k2_tarski(C_383, D_384), C_385), A_142) | r2_yellow_0(k2_yellow_1(A_142), k2_tarski(C_383, D_384)) | ~r1_lattice3(k2_yellow_1(A_142), k2_tarski(C_383, D_384), C_385) | ~m1_subset_1(C_385, u1_struct_0(k2_yellow_1(A_142))) | ~l1_orders_2(k2_yellow_1(A_142)) | ~v5_orders_2(k2_yellow_1(A_142)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_1304])).
% 9.92/3.46  tff(c_2503, plain, (![A_516, C_517, D_518, C_519]: (r1_orders_2(k2_yellow_1(A_516), '#skF_1'(k2_yellow_1(A_516), k2_tarski(C_517, D_518), C_519), C_517) | ~m1_subset_1(D_518, A_516) | ~m1_subset_1(C_517, A_516) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_516), k2_tarski(C_517, D_518), C_519), A_516) | r2_yellow_0(k2_yellow_1(A_516), k2_tarski(C_517, D_518)) | ~r1_lattice3(k2_yellow_1(A_516), k2_tarski(C_517, D_518), C_519) | ~m1_subset_1(C_519, A_516))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_253, c_253, c_253, c_1309])).
% 9.92/3.46  tff(c_3466, plain, (![A_672, C_673, D_674, C_675]: (r1_tarski('#skF_1'(k2_yellow_1(A_672), k2_tarski(C_673, D_674), C_675), C_673) | v1_xboole_0(A_672) | v2_struct_0(k2_yellow_1(A_672)) | ~m1_subset_1(D_674, A_672) | ~m1_subset_1(C_673, A_672) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_672), k2_tarski(C_673, D_674), C_675), A_672) | r2_yellow_0(k2_yellow_1(A_672), k2_tarski(C_673, D_674)) | ~r1_lattice3(k2_yellow_1(A_672), k2_tarski(C_673, D_674), C_675) | ~m1_subset_1(C_675, A_672))), inference(resolution, [status(thm)], [c_2503, c_539])).
% 9.92/3.46  tff(c_3470, plain, (![A_142, C_673, D_674, C_200]: (r1_tarski('#skF_1'(k2_yellow_1(A_142), k2_tarski(C_673, D_674), C_200), C_673) | v1_xboole_0(A_142) | v2_struct_0(k2_yellow_1(A_142)) | ~m1_subset_1(D_674, A_142) | ~m1_subset_1(C_673, A_142) | r2_yellow_0(k2_yellow_1(A_142), k2_tarski(C_673, D_674)) | ~r1_lattice3(k2_yellow_1(A_142), k2_tarski(C_673, D_674), C_200) | ~m1_subset_1(C_200, A_142))), inference(resolution, [status(thm)], [c_471, c_3466])).
% 9.92/3.46  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.92/3.46  tff(c_540, plain, (![A_216, B_217, C_218]: (~r1_orders_2(A_216, '#skF_1'(A_216, B_217, C_218), C_218) | r2_yellow_0(A_216, B_217) | ~r1_lattice3(A_216, B_217, C_218) | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~l1_orders_2(A_216) | ~v5_orders_2(A_216))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.92/3.46  tff(c_544, plain, (![A_79, B_217, C_85]: (r2_yellow_0(k2_yellow_1(A_79), B_217) | ~r1_lattice3(k2_yellow_1(A_79), B_217, C_85) | ~m1_subset_1(C_85, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)) | v2_struct_0(k2_yellow_1(A_79)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_79), B_217, C_85), C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_79), B_217, C_85), A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_488, c_540])).
% 9.92/3.46  tff(c_831, plain, (![A_287, B_288, C_289]: (r2_yellow_0(k2_yellow_1(A_287), B_288) | ~r1_lattice3(k2_yellow_1(A_287), B_288, C_289) | v2_struct_0(k2_yellow_1(A_287)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_287), B_288, C_289), C_289) | ~m1_subset_1(C_289, A_287) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_287), B_288, C_289), A_287) | v1_xboole_0(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68, c_253, c_544])).
% 9.92/3.46  tff(c_4531, plain, (![A_785, B_786, B_787, C_788]: (r2_yellow_0(k2_yellow_1(A_785), B_786) | ~r1_lattice3(k2_yellow_1(A_785), B_786, k3_xboole_0(B_787, C_788)) | v2_struct_0(k2_yellow_1(A_785)) | ~m1_subset_1(k3_xboole_0(B_787, C_788), A_785) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_785), B_786, k3_xboole_0(B_787, C_788)), A_785) | v1_xboole_0(A_785) | ~r1_tarski('#skF_1'(k2_yellow_1(A_785), B_786, k3_xboole_0(B_787, C_788)), C_788) | ~r1_tarski('#skF_1'(k2_yellow_1(A_785), B_786, k3_xboole_0(B_787, C_788)), B_787))), inference(resolution, [status(thm)], [c_6, c_831])).
% 9.92/3.46  tff(c_4540, plain, (![A_789, B_790, B_791, C_792]: (v2_struct_0(k2_yellow_1(A_789)) | v1_xboole_0(A_789) | ~r1_tarski('#skF_1'(k2_yellow_1(A_789), B_790, k3_xboole_0(B_791, C_792)), C_792) | ~r1_tarski('#skF_1'(k2_yellow_1(A_789), B_790, k3_xboole_0(B_791, C_792)), B_791) | r2_yellow_0(k2_yellow_1(A_789), B_790) | ~r1_lattice3(k2_yellow_1(A_789), B_790, k3_xboole_0(B_791, C_792)) | ~m1_subset_1(k3_xboole_0(B_791, C_792), A_789))), inference(resolution, [status(thm)], [c_471, c_4531])).
% 9.92/3.46  tff(c_4615, plain, (![A_800, C_801, D_802, B_803]: (~r1_tarski('#skF_1'(k2_yellow_1(A_800), k2_tarski(C_801, D_802), k3_xboole_0(B_803, C_801)), B_803) | v1_xboole_0(A_800) | v2_struct_0(k2_yellow_1(A_800)) | ~m1_subset_1(D_802, A_800) | ~m1_subset_1(C_801, A_800) | r2_yellow_0(k2_yellow_1(A_800), k2_tarski(C_801, D_802)) | ~r1_lattice3(k2_yellow_1(A_800), k2_tarski(C_801, D_802), k3_xboole_0(B_803, C_801)) | ~m1_subset_1(k3_xboole_0(B_803, C_801), A_800))), inference(resolution, [status(thm)], [c_3470, c_4540])).
% 9.92/3.46  tff(c_4642, plain, (![A_804, D_805, C_806]: (v1_xboole_0(A_804) | v2_struct_0(k2_yellow_1(A_804)) | ~m1_subset_1(D_805, A_804) | ~m1_subset_1(C_806, A_804) | r2_yellow_0(k2_yellow_1(A_804), k2_tarski(C_806, D_805)) | ~r1_lattice3(k2_yellow_1(A_804), k2_tarski(C_806, D_805), k3_xboole_0(D_805, C_806)) | ~m1_subset_1(k3_xboole_0(D_805, C_806), A_804))), inference(resolution, [status(thm)], [c_3507, c_4615])).
% 9.92/3.46  tff(c_4646, plain, (![A_804, D_73, C_71]: (v1_xboole_0(A_804) | v2_struct_0(k2_yellow_1(A_804)) | ~m1_subset_1(D_73, A_804) | ~m1_subset_1(C_71, A_804) | r2_yellow_0(k2_yellow_1(A_804), k2_tarski(C_71, D_73)) | ~m1_subset_1(k3_xboole_0(D_73, C_71), A_804) | ~r1_orders_2(k2_yellow_1(A_804), k3_xboole_0(D_73, C_71), D_73) | ~r1_orders_2(k2_yellow_1(A_804), k3_xboole_0(D_73, C_71), C_71) | ~m1_subset_1(D_73, u1_struct_0(k2_yellow_1(A_804))) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_804))) | ~m1_subset_1(k3_xboole_0(D_73, C_71), u1_struct_0(k2_yellow_1(A_804))) | ~l1_orders_2(k2_yellow_1(A_804)))), inference(resolution, [status(thm)], [c_44, c_4642])).
% 9.92/3.46  tff(c_4973, plain, (![A_827, C_828, D_829]: (v1_xboole_0(A_827) | v2_struct_0(k2_yellow_1(A_827)) | r2_yellow_0(k2_yellow_1(A_827), k2_tarski(C_828, D_829)) | ~r1_orders_2(k2_yellow_1(A_827), k3_xboole_0(D_829, C_828), D_829) | ~r1_orders_2(k2_yellow_1(A_827), k3_xboole_0(D_829, C_828), C_828) | ~m1_subset_1(D_829, A_827) | ~m1_subset_1(C_828, A_827) | ~m1_subset_1(k3_xboole_0(D_829, C_828), A_827))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_253, c_253, c_253, c_4646])).
% 9.92/3.46  tff(c_4994, plain, (![A_79, C_828, C_85]: (r2_yellow_0(k2_yellow_1(A_79), k2_tarski(C_828, C_85)) | ~r1_orders_2(k2_yellow_1(A_79), k3_xboole_0(C_85, C_828), C_828) | ~m1_subset_1(C_828, A_79) | v2_struct_0(k2_yellow_1(A_79)) | ~r1_tarski(k3_xboole_0(C_85, C_828), C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(k3_xboole_0(C_85, C_828), A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_488, c_4973])).
% 9.92/3.46  tff(c_5028, plain, (![A_833, C_834, C_835]: (r2_yellow_0(k2_yellow_1(A_833), k2_tarski(C_834, C_835)) | ~r1_orders_2(k2_yellow_1(A_833), k3_xboole_0(C_835, C_834), C_834) | ~m1_subset_1(C_834, A_833) | v2_struct_0(k2_yellow_1(A_833)) | ~m1_subset_1(C_835, A_833) | ~m1_subset_1(k3_xboole_0(C_835, C_834), A_833) | v1_xboole_0(A_833))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4994])).
% 9.92/3.46  tff(c_5056, plain, (![A_79, C_85, C_835]: (r2_yellow_0(k2_yellow_1(A_79), k2_tarski(C_85, C_835)) | ~m1_subset_1(C_835, A_79) | v2_struct_0(k2_yellow_1(A_79)) | ~r1_tarski(k3_xboole_0(C_835, C_85), C_85) | ~m1_subset_1(C_85, A_79) | ~m1_subset_1(k3_xboole_0(C_835, C_85), A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_488, c_5028])).
% 9.92/3.46  tff(c_5092, plain, (![A_836, C_837, C_838]: (r2_yellow_0(k2_yellow_1(A_836), k2_tarski(C_837, C_838)) | ~m1_subset_1(C_838, A_836) | v2_struct_0(k2_yellow_1(A_836)) | ~m1_subset_1(C_837, A_836) | ~m1_subset_1(k3_xboole_0(C_838, C_837), A_836) | v1_xboole_0(A_836))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_5056])).
% 9.92/3.46  tff(c_36, plain, (![A_48]: (~r2_yellow_0(A_48, k2_tarski('#skF_3'(A_48), '#skF_4'(A_48))) | v2_lattice3(A_48) | ~l1_orders_2(A_48) | ~v5_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.92/3.46  tff(c_5100, plain, (![A_836]: (v2_lattice3(k2_yellow_1(A_836)) | ~l1_orders_2(k2_yellow_1(A_836)) | ~v5_orders_2(k2_yellow_1(A_836)) | ~m1_subset_1('#skF_4'(k2_yellow_1(A_836)), A_836) | v2_struct_0(k2_yellow_1(A_836)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_836)), A_836) | ~m1_subset_1(k3_xboole_0('#skF_4'(k2_yellow_1(A_836)), '#skF_3'(k2_yellow_1(A_836))), A_836) | v1_xboole_0(A_836))), inference(resolution, [status(thm)], [c_5092, c_36])).
% 9.92/3.46  tff(c_5139, plain, (![A_845]: (v2_lattice3(k2_yellow_1(A_845)) | ~m1_subset_1('#skF_4'(k2_yellow_1(A_845)), A_845) | v2_struct_0(k2_yellow_1(A_845)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_845)), A_845) | ~m1_subset_1(k3_xboole_0('#skF_3'(k2_yellow_1(A_845)), '#skF_4'(k2_yellow_1(A_845))), A_845) | v1_xboole_0(A_845))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76, c_68, c_5100])).
% 9.92/3.46  tff(c_5143, plain, (v2_lattice3(k2_yellow_1('#skF_5')) | v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5') | ~r2_hidden('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~r2_hidden('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_645, c_5139])).
% 9.92/3.46  tff(c_5146, plain, (~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5') | ~r2_hidden('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~r2_hidden('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_900, c_88, c_5143])).
% 9.92/3.46  tff(c_5147, plain, (~r2_hidden('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_5146])).
% 9.92/3.46  tff(c_5150, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_8, c_5147])).
% 9.92/3.46  tff(c_5153, plain, (~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_5150])).
% 9.92/3.46  tff(c_5156, plain, (v2_lattice3(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_278, c_5153])).
% 9.92/3.46  tff(c_5160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5156])).
% 9.92/3.46  tff(c_5161, plain, (~r2_hidden('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_5146])).
% 9.92/3.46  tff(c_5164, plain, (~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_5161])).
% 9.92/3.46  tff(c_5167, plain, (v2_lattice3(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_280, c_5164])).
% 9.92/3.46  tff(c_5171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5167])).
% 9.92/3.46  tff(c_5173, plain, (m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_5161])).
% 9.92/3.46  tff(c_5172, plain, (~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5') | ~r2_hidden('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_5161])).
% 9.92/3.46  tff(c_5323, plain, (~r2_hidden('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_5172])).
% 9.92/3.46  tff(c_5326, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5')), '#skF_5')), inference(resolution, [status(thm)], [c_8, c_5323])).
% 9.92/3.46  tff(c_5329, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_5326])).
% 9.92/3.46  tff(c_5331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_5329])).
% 9.92/3.46  tff(c_5332, plain, (~m1_subset_1('#skF_3'(k2_yellow_1('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_5172])).
% 9.92/3.46  tff(c_5336, plain, (v2_lattice3(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_278, c_5332])).
% 9.92/3.46  tff(c_5340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5336])).
% 9.92/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.46  
% 9.92/3.46  Inference rules
% 9.92/3.46  ----------------------
% 9.92/3.46  #Ref     : 11
% 9.92/3.46  #Sup     : 1118
% 9.92/3.46  #Fact    : 0
% 9.92/3.46  #Define  : 0
% 9.92/3.46  #Split   : 4
% 9.92/3.46  #Chain   : 0
% 9.92/3.46  #Close   : 0
% 9.92/3.46  
% 9.92/3.46  Ordering : KBO
% 9.92/3.46  
% 9.92/3.46  Simplification rules
% 9.92/3.46  ----------------------
% 9.92/3.46  #Subsume      : 351
% 9.92/3.46  #Demod        : 2527
% 9.92/3.46  #Tautology    : 265
% 9.92/3.46  #SimpNegUnit  : 57
% 9.92/3.46  #BackRed      : 2
% 9.92/3.46  
% 9.92/3.46  #Partial instantiations: 0
% 9.92/3.46  #Strategies tried      : 1
% 9.92/3.46  
% 9.92/3.46  Timing (in seconds)
% 9.92/3.46  ----------------------
% 9.92/3.46  Preprocessing        : 0.38
% 9.92/3.46  Parsing              : 0.20
% 9.92/3.46  CNF conversion       : 0.04
% 9.92/3.46  Main loop            : 2.27
% 9.92/3.46  Inferencing          : 0.69
% 9.92/3.46  Reduction            : 0.75
% 9.92/3.46  Demodulation         : 0.59
% 9.92/3.46  BG Simplification    : 0.06
% 9.92/3.46  Subsumption          : 0.66
% 9.92/3.46  Abstraction          : 0.08
% 9.92/3.46  MUC search           : 0.00
% 9.92/3.46  Cooper               : 0.00
% 9.92/3.46  Total                : 2.71
% 9.92/3.46  Index Insertion      : 0.00
% 9.92/3.46  Index Deletion       : 0.00
% 9.92/3.46  Index Matching       : 0.00
% 9.92/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
