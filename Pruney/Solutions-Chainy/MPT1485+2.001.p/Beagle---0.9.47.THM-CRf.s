%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:40 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  220 (2552 expanded)
%              Number of leaves         :   48 ( 943 expanded)
%              Depth                    :   28
%              Number of atoms          :  654 (11391 expanded)
%              Number of equality atoms :   93 (1337 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_relat_1 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff(f_227,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k12_lattice3(A,B,k13_lattice3(A,B,C)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_184,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_196,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

tff(f_208,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_74,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_76,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_24,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_80,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_745,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( m1_subset_1('#skF_3'(A_235,B_236,C_237,D_238),u1_struct_0(A_235))
      | k11_lattice3(A_235,B_236,C_237) = D_238
      | ~ r1_orders_2(A_235,D_238,C_237)
      | ~ r1_orders_2(A_235,D_238,B_236)
      | ~ m1_subset_1(D_238,u1_struct_0(A_235))
      | ~ m1_subset_1(C_237,u1_struct_0(A_235))
      | ~ m1_subset_1(B_236,u1_struct_0(A_235))
      | ~ l1_orders_2(A_235)
      | ~ v2_lattice3(A_235)
      | ~ v5_orders_2(A_235)
      | v2_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_34,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k10_lattice3(A_34,B_35,C_36),u1_struct_0(A_34))
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_309,plain,(
    ! [A_191,B_192,C_193] :
      ( k12_lattice3(A_191,B_192,C_193) = k11_lattice3(A_191,B_192,C_193)
      | ~ m1_subset_1(C_193,u1_struct_0(A_191))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | ~ v2_lattice3(A_191)
      | ~ v5_orders_2(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_313,plain,(
    ! [B_192] :
      ( k12_lattice3('#skF_4',B_192,'#skF_5') = k11_lattice3('#skF_4',B_192,'#skF_5')
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_309])).

tff(c_373,plain,(
    ! [B_198] :
      ( k12_lattice3('#skF_4',B_198,'#skF_5') = k11_lattice3('#skF_4',B_198,'#skF_5')
      | ~ m1_subset_1(B_198,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_313])).

tff(c_377,plain,(
    ! [B_35,C_36] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_5')
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_373])).

tff(c_630,plain,(
    ! [B_223,C_224] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_223,C_224),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_223,C_224),'#skF_5')
      | ~ m1_subset_1(C_224,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_377])).

tff(c_642,plain,(
    ! [B_223] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_223,'#skF_6'),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_223,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_630])).

tff(c_760,plain,(
    ! [B_236,C_237,D_238] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_3'('#skF_4',B_236,C_237,D_238),'#skF_6'),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_3'('#skF_4',B_236,C_237,D_238),'#skF_6'),'#skF_5')
      | k11_lattice3('#skF_4',B_236,C_237) = D_238
      | ~ r1_orders_2('#skF_4',D_238,C_237)
      | ~ r1_orders_2('#skF_4',D_238,B_236)
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_237,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_236,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_745,c_642])).

tff(c_844,plain,(
    ! [B_236,C_237,D_238] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_3'('#skF_4',B_236,C_237,D_238),'#skF_6'),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_3'('#skF_4',B_236,C_237,D_238),'#skF_6'),'#skF_5')
      | k11_lattice3('#skF_4',B_236,C_237) = D_238
      | ~ r1_orders_2('#skF_4',D_238,C_237)
      | ~ r1_orders_2('#skF_4',D_238,B_236)
      | ~ m1_subset_1(D_238,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_237,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_236,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_760])).

tff(c_1316,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_30,plain,(
    ! [A_30] :
      ( ~ v2_struct_0(A_30)
      | ~ v2_lattice3(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1319,plain,
    ( ~ v2_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_1316,c_30])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_1319])).

tff(c_1328,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_78,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_427,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_orders_2(A_200,B_201,k10_lattice3(A_200,B_201,C_202))
      | ~ m1_subset_1(k10_lattice3(A_200,B_201,C_202),u1_struct_0(A_200))
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v1_lattice3(A_200)
      | ~ v5_orders_2(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_430,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_orders_2(A_34,B_35,k10_lattice3(A_34,B_35,C_36))
      | ~ v1_lattice3(A_34)
      | ~ v5_orders_2(A_34)
      | v2_struct_0(A_34)
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_34,c_427])).

tff(c_1349,plain,(
    ! [A_307,B_308,B_309,C_310] :
      ( k12_lattice3(A_307,B_308,k10_lattice3(A_307,B_309,C_310)) = k11_lattice3(A_307,B_308,k10_lattice3(A_307,B_309,C_310))
      | ~ m1_subset_1(B_308,u1_struct_0(A_307))
      | ~ v2_lattice3(A_307)
      | ~ v5_orders_2(A_307)
      | ~ m1_subset_1(C_310,u1_struct_0(A_307))
      | ~ m1_subset_1(B_309,u1_struct_0(A_307))
      | ~ l1_orders_2(A_307) ) ),
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_1357,plain,(
    ! [B_309,C_310] :
      ( k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_309,C_310)) = k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_309,C_310))
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ m1_subset_1(C_310,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_1349])).

tff(c_1369,plain,(
    ! [B_311,C_312] :
      ( k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_311,C_312)) = k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_311,C_312))
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_76,c_1357])).

tff(c_1444,plain,(
    ! [B_318] :
      ( k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_318,'#skF_6')) = k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_318,'#skF_6'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_1369])).

tff(c_1474,plain,(
    k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) = k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_1444])).

tff(c_668,plain,(
    ! [B_230] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_230,'#skF_6'),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_230,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(B_230,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_630])).

tff(c_682,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_668])).

tff(c_228,plain,(
    ! [A_184,C_185,B_186] :
      ( k12_lattice3(A_184,C_185,B_186) = k12_lattice3(A_184,B_186,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_184))
      | ~ m1_subset_1(B_186,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v2_lattice3(A_184)
      | ~ v5_orders_2(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_232,plain,(
    ! [B_186] :
      ( k12_lattice3('#skF_4',B_186,'#skF_5') = k12_lattice3('#skF_4','#skF_5',B_186)
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_228])).

tff(c_246,plain,(
    ! [B_187] :
      ( k12_lattice3('#skF_4',B_187,'#skF_5') = k12_lattice3('#skF_4','#skF_5',B_187)
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_232])).

tff(c_250,plain,(
    ! [B_35,C_36] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_5') = k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_246])).

tff(c_908,plain,(
    ! [B_239,C_240] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_239,C_240),'#skF_5') = k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_239,C_240))
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_250])).

tff(c_960,plain,(
    ! [B_242] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_242,'#skF_6'),'#skF_5') = k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4',B_242,'#skF_6'))
      | ~ m1_subset_1(B_242,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_908])).

tff(c_971,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') = k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_960])).

tff(c_982,plain,(
    k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_971])).

tff(c_1506,plain,(
    k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') = k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_982])).

tff(c_169,plain,(
    ! [A_179,B_180,C_181] :
      ( k13_lattice3(A_179,B_180,C_181) = k10_lattice3(A_179,B_180,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | ~ v1_lattice3(A_179)
      | ~ v5_orders_2(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_175,plain,(
    ! [B_180] :
      ( k13_lattice3('#skF_4',B_180,'#skF_6') = k10_lattice3('#skF_4',B_180,'#skF_6')
      | ~ m1_subset_1(B_180,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_169])).

tff(c_207,plain,(
    ! [B_183] :
      ( k13_lattice3('#skF_4',B_183,'#skF_6') = k10_lattice3('#skF_4',B_183,'#skF_6')
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_175])).

tff(c_221,plain,(
    k13_lattice3('#skF_4','#skF_5','#skF_6') = k10_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_207])).

tff(c_68,plain,(
    k12_lattice3('#skF_4','#skF_5',k13_lattice3('#skF_4','#skF_5','#skF_6')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_223,plain,(
    k12_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_68])).

tff(c_985,plain,(
    k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_223])).

tff(c_1545,plain,(
    k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_985])).

tff(c_369,plain,(
    ! [A_195,C_196,B_197] :
      ( r1_orders_2(A_195,C_196,k10_lattice3(A_195,B_197,C_196))
      | ~ m1_subset_1(k10_lattice3(A_195,B_197,C_196),u1_struct_0(A_195))
      | ~ m1_subset_1(C_196,u1_struct_0(A_195))
      | ~ m1_subset_1(B_197,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v1_lattice3(A_195)
      | ~ v5_orders_2(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_372,plain,(
    ! [A_34,C_36,B_35] :
      ( r1_orders_2(A_34,C_36,k10_lattice3(A_34,B_35,C_36))
      | ~ v1_lattice3(A_34)
      | ~ v5_orders_2(A_34)
      | v2_struct_0(A_34)
      | ~ m1_subset_1(C_36,u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_34,c_369])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_153] :
      ( m1_subset_1(u1_orders_2(A_153),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153),u1_struct_0(A_153))))
      | ~ l1_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_153] :
      ( v1_relat_1(u1_orders_2(A_153))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_153),u1_struct_0(A_153)))
      | ~ l1_orders_2(A_153) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_103,plain,(
    ! [A_153] :
      ( v1_relat_1(u1_orders_2(A_153))
      | ~ l1_orders_2(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_82,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_18,plain,(
    ! [A_19] :
      ( r1_relat_2(u1_orders_2(A_19),u1_struct_0(A_19))
      | ~ v3_orders_2(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [C_154,A_155,B_156] :
      ( r2_hidden(k4_tarski(C_154,C_154),A_155)
      | ~ r2_hidden(C_154,B_156)
      | ~ r1_relat_2(A_155,B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [A_160,A_161,B_162] :
      ( r2_hidden(k4_tarski(A_160,A_160),A_161)
      | ~ r1_relat_2(A_161,B_162)
      | ~ v1_relat_1(A_161)
      | v1_xboole_0(B_162)
      | ~ m1_subset_1(A_160,B_162) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_156,plain,(
    ! [A_177,A_178] :
      ( r2_hidden(k4_tarski(A_177,A_177),u1_orders_2(A_178))
      | ~ v1_relat_1(u1_orders_2(A_178))
      | v1_xboole_0(u1_struct_0(A_178))
      | ~ m1_subset_1(A_177,u1_struct_0(A_178))
      | ~ v3_orders_2(A_178)
      | ~ l1_orders_2(A_178) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_20,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_orders_2(A_20,B_24,C_26)
      | ~ r2_hidden(k4_tarski(B_24,C_26),u1_orders_2(A_20))
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ! [A_189,A_190] :
      ( r1_orders_2(A_189,A_190,A_190)
      | ~ v1_relat_1(u1_orders_2(A_189))
      | v1_xboole_0(u1_struct_0(A_189))
      | ~ m1_subset_1(A_190,u1_struct_0(A_189))
      | ~ v3_orders_2(A_189)
      | ~ l1_orders_2(A_189) ) ),
    inference(resolution,[status(thm)],[c_156,c_20])).

tff(c_289,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v3_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_285])).

tff(c_295,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82,c_289])).

tff(c_299,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_302,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_299])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_302])).

tff(c_308,plain,(
    v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_291,plain,
    ( r1_orders_2('#skF_4','#skF_6','#skF_6')
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v3_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_285])).

tff(c_298,plain,
    ( r1_orders_2('#skF_4','#skF_6','#skF_6')
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82,c_291])).

tff(c_325,plain,
    ( r1_orders_2('#skF_4','#skF_6','#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_298])).

tff(c_326,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_14,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_346,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_326,c_14])).

tff(c_347,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_350,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_347])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_350])).

tff(c_355,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_359,plain,
    ( ~ v2_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_30])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_359])).

tff(c_367,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_52,plain,(
    ! [A_83,B_107,C_119,D_125] :
      ( r1_orders_2(A_83,'#skF_3'(A_83,B_107,C_119,D_125),C_119)
      | k11_lattice3(A_83,B_107,C_119) = D_125
      | ~ r1_orders_2(A_83,D_125,C_119)
      | ~ r1_orders_2(A_83,D_125,B_107)
      | ~ m1_subset_1(D_125,u1_struct_0(A_83))
      | ~ m1_subset_1(C_119,u1_struct_0(A_83))
      | ~ m1_subset_1(B_107,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83)
      | ~ v2_lattice3(A_83)
      | ~ v5_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1633,plain,(
    ! [A_326,B_327,C_328,D_329] :
      ( ~ r1_orders_2(A_326,'#skF_3'(A_326,B_327,C_328,D_329),D_329)
      | k11_lattice3(A_326,B_327,C_328) = D_329
      | ~ r1_orders_2(A_326,D_329,C_328)
      | ~ r1_orders_2(A_326,D_329,B_327)
      | ~ m1_subset_1(D_329,u1_struct_0(A_326))
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ m1_subset_1(B_327,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326)
      | ~ v2_lattice3(A_326)
      | ~ v5_orders_2(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2810,plain,(
    ! [A_357,B_358,C_359] :
      ( k11_lattice3(A_357,B_358,C_359) = C_359
      | ~ r1_orders_2(A_357,C_359,C_359)
      | ~ r1_orders_2(A_357,C_359,B_358)
      | ~ m1_subset_1(C_359,u1_struct_0(A_357))
      | ~ m1_subset_1(B_358,u1_struct_0(A_357))
      | ~ l1_orders_2(A_357)
      | ~ v2_lattice3(A_357)
      | ~ v5_orders_2(A_357)
      | v2_struct_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_52,c_1633])).

tff(c_2816,plain,(
    ! [B_358] :
      ( k11_lattice3('#skF_4',B_358,'#skF_6') = '#skF_6'
      | ~ r1_orders_2('#skF_4','#skF_6',B_358)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_367,c_2810])).

tff(c_2823,plain,(
    ! [B_358] :
      ( k11_lattice3('#skF_4',B_358,'#skF_6') = '#skF_6'
      | ~ r1_orders_2('#skF_4','#skF_6',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2816])).

tff(c_2829,plain,(
    ! [B_360] :
      ( k11_lattice3('#skF_4',B_360,'#skF_6') = '#skF_6'
      | ~ r1_orders_2('#skF_4','#skF_6',B_360)
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_2823])).

tff(c_2841,plain,(
    ! [B_35,C_36] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_6') = '#skF_6'
      | ~ r1_orders_2('#skF_4','#skF_6',k10_lattice3('#skF_4',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_2829])).

tff(c_3284,plain,(
    ! [B_390,C_391] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_390,C_391),'#skF_6') = '#skF_6'
      | ~ r1_orders_2('#skF_4','#skF_6',k10_lattice3('#skF_4',B_390,C_391))
      | ~ m1_subset_1(C_391,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_390,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2841])).

tff(c_3298,plain,(
    ! [B_35] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_372,c_3284])).

tff(c_3309,plain,(
    ! [B_35] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,'#skF_6'),'#skF_6') = '#skF_6'
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_80,c_78,c_3298])).

tff(c_3394,plain,(
    ! [B_393] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_393,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_393,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_3309])).

tff(c_3424,plain,(
    k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_72,c_3394])).

tff(c_1359,plain,(
    ! [B_309,C_310] :
      ( k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_309,C_310)) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_309,C_310))
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ m1_subset_1(C_310,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_1349])).

tff(c_1569,plain,(
    ! [B_323,C_324] :
      ( k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_323,C_324)) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_323,C_324))
      | ~ m1_subset_1(C_324,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_76,c_1359])).

tff(c_1679,plain,(
    ! [B_330] :
      ( k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_330,'#skF_6')) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_330,'#skF_6'))
      | ~ m1_subset_1(B_330,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_1569])).

tff(c_1709,plain,(
    k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_1679])).

tff(c_315,plain,(
    ! [B_192] :
      ( k12_lattice3('#skF_4',B_192,'#skF_6') = k11_lattice3('#skF_4',B_192,'#skF_6')
      | ~ m1_subset_1(B_192,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_309])).

tff(c_402,plain,(
    ! [B_199] :
      ( k12_lattice3('#skF_4',B_199,'#skF_6') = k11_lattice3('#skF_4',B_199,'#skF_6')
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_315])).

tff(c_406,plain,(
    ! [B_35,C_36] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_6')
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_402])).

tff(c_432,plain,(
    ! [B_205,C_206] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_205,C_206),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_205,C_206),'#skF_6')
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_205,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_406])).

tff(c_469,plain,(
    ! [B_208] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_208,'#skF_6'),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_208,'#skF_6'),'#skF_6')
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_432])).

tff(c_483,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_469])).

tff(c_234,plain,(
    ! [B_186] :
      ( k12_lattice3('#skF_4',B_186,'#skF_6') = k12_lattice3('#skF_4','#skF_6',B_186)
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_228])).

tff(c_267,plain,(
    ! [B_188] :
      ( k12_lattice3('#skF_4',B_188,'#skF_6') = k12_lattice3('#skF_4','#skF_6',B_188)
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_234])).

tff(c_271,plain,(
    ! [B_35,C_36] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_35,C_36),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_35,C_36))
      | ~ m1_subset_1(C_36,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_267])).

tff(c_560,plain,(
    ! [B_216,C_217] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_216,C_217),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_216,C_217))
      | ~ m1_subset_1(C_217,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_271])).

tff(c_604,plain,(
    ! [B_222] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_222,'#skF_6'),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_222,'#skF_6'))
      | ~ m1_subset_1(B_222,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_70,c_560])).

tff(c_611,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_604])).

tff(c_619,plain,(
    k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_611])).

tff(c_1719,plain,(
    k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_6'),'#skF_6') = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_619])).

tff(c_3427,plain,(
    k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_1719])).

tff(c_60,plain,(
    ! [A_83,B_107,C_119] :
      ( r1_orders_2(A_83,k11_lattice3(A_83,B_107,C_119),C_119)
      | ~ m1_subset_1(k11_lattice3(A_83,B_107,C_119),u1_struct_0(A_83))
      | ~ m1_subset_1(C_119,u1_struct_0(A_83))
      | ~ m1_subset_1(B_107,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83)
      | ~ v2_lattice3(A_83)
      | ~ v5_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_3477,plain,
    ( r1_orders_2('#skF_4',k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6')),k10_lattice3('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3427,c_60])).

tff(c_3487,plain,
    ( r1_orders_2('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_70,c_3427,c_3477])).

tff(c_3488,plain,
    ( r1_orders_2('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_3487])).

tff(c_3847,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3488])).

tff(c_3875,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_3847])).

tff(c_3879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3875])).

tff(c_3881,plain,(
    m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_307,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_323,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_1396,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( r1_orders_2(A_313,B_314,'#skF_2'(A_313,B_314,C_315,D_316))
      | k10_lattice3(A_313,B_314,C_315) = D_316
      | ~ r1_orders_2(A_313,C_315,D_316)
      | ~ r1_orders_2(A_313,B_314,D_316)
      | ~ m1_subset_1(D_316,u1_struct_0(A_313))
      | ~ m1_subset_1(C_315,u1_struct_0(A_313))
      | ~ m1_subset_1(B_314,u1_struct_0(A_313))
      | ~ l1_orders_2(A_313)
      | ~ v1_lattice3(A_313)
      | ~ v5_orders_2(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    ! [A_37,D_79,B_61,C_73] :
      ( ~ r1_orders_2(A_37,D_79,'#skF_2'(A_37,B_61,C_73,D_79))
      | k10_lattice3(A_37,B_61,C_73) = D_79
      | ~ r1_orders_2(A_37,C_73,D_79)
      | ~ r1_orders_2(A_37,B_61,D_79)
      | ~ m1_subset_1(D_79,u1_struct_0(A_37))
      | ~ m1_subset_1(C_73,u1_struct_0(A_37))
      | ~ m1_subset_1(B_61,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v1_lattice3(A_37)
      | ~ v5_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2570,plain,(
    ! [A_353,D_354,C_355] :
      ( k10_lattice3(A_353,D_354,C_355) = D_354
      | ~ r1_orders_2(A_353,C_355,D_354)
      | ~ r1_orders_2(A_353,D_354,D_354)
      | ~ m1_subset_1(C_355,u1_struct_0(A_353))
      | ~ m1_subset_1(D_354,u1_struct_0(A_353))
      | ~ l1_orders_2(A_353)
      | ~ v1_lattice3(A_353)
      | ~ v5_orders_2(A_353)
      | v2_struct_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_1396,c_36])).

tff(c_2596,plain,
    ( k10_lattice3('#skF_4','#skF_5','#skF_5') = '#skF_5'
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_323,c_2570])).

tff(c_2623,plain,
    ( k10_lattice3('#skF_4','#skF_5','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_323,c_2596])).

tff(c_2624,plain,(
    k10_lattice3('#skF_4','#skF_5','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_2623])).

tff(c_1596,plain,(
    ! [B_325] :
      ( k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_325,'#skF_5')) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_325,'#skF_5'))
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_72,c_1569])).

tff(c_1626,plain,(
    k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')) = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_1596])).

tff(c_445,plain,(
    ! [B_207] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_207,'#skF_5'),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4',B_207,'#skF_5'),'#skF_6')
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_72,c_432])).

tff(c_459,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6') = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_445])).

tff(c_578,plain,(
    ! [B_221] :
      ( k12_lattice3('#skF_4',k10_lattice3('#skF_4',B_221,'#skF_5'),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4',B_221,'#skF_5'))
      | ~ m1_subset_1(B_221,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_72,c_560])).

tff(c_585,plain,(
    k12_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6') = k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_578])).

tff(c_593,plain,(
    k12_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')) = k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_585])).

tff(c_1628,plain,(
    k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6') = k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_593])).

tff(c_1654,plain,
    ( r1_orders_2('#skF_4',k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1(k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1628,c_60])).

tff(c_1661,plain,
    ( r1_orders_2('#skF_4',k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')),'#skF_6')
    | ~ m1_subset_1(k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1628,c_1654])).

tff(c_1662,plain,
    ( r1_orders_2('#skF_4',k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')),'#skF_6')
    | ~ m1_subset_1(k11_lattice3('#skF_4','#skF_6',k10_lattice3('#skF_4','#skF_5','#skF_5')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_1661])).

tff(c_1822,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1662])).

tff(c_1825,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1822])).

tff(c_1829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1825])).

tff(c_1831,plain,(
    m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1662])).

tff(c_368,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_166,plain,(
    ! [A_178,A_177] :
      ( r1_orders_2(A_178,A_177,A_177)
      | ~ v1_relat_1(u1_orders_2(A_178))
      | v1_xboole_0(u1_struct_0(A_178))
      | ~ m1_subset_1(A_177,u1_struct_0(A_178))
      | ~ v3_orders_2(A_178)
      | ~ l1_orders_2(A_178) ) ),
    inference(resolution,[status(thm)],[c_156,c_20])).

tff(c_1909,plain,
    ( r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),k10_lattice3('#skF_4','#skF_5','#skF_5'))
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v3_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_1831,c_166])).

tff(c_1965,plain,
    ( r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),k10_lattice3('#skF_4','#skF_5','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82,c_308,c_1909])).

tff(c_1966,plain,(
    r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),k10_lattice3('#skF_4','#skF_5','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_1965])).

tff(c_2019,plain,(
    ! [A_338,B_339,C_340,E_341] :
      ( r1_orders_2(A_338,k10_lattice3(A_338,B_339,C_340),E_341)
      | ~ r1_orders_2(A_338,C_340,E_341)
      | ~ r1_orders_2(A_338,B_339,E_341)
      | ~ m1_subset_1(E_341,u1_struct_0(A_338))
      | ~ m1_subset_1(k10_lattice3(A_338,B_339,C_340),u1_struct_0(A_338))
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ m1_subset_1(B_339,u1_struct_0(A_338))
      | ~ l1_orders_2(A_338)
      | ~ v1_lattice3(A_338)
      | ~ v5_orders_2(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2021,plain,(
    ! [E_341] :
      ( r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341)
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1831,c_2019])).

tff(c_2026,plain,(
    ! [E_341] :
      ( r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341)
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_2021])).

tff(c_2027,plain,(
    ! [E_341] :
      ( r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341)
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_2026])).

tff(c_54,plain,(
    ! [A_83,B_107,C_119,D_125] :
      ( r1_orders_2(A_83,'#skF_3'(A_83,B_107,C_119,D_125),B_107)
      | k11_lattice3(A_83,B_107,C_119) = D_125
      | ~ r1_orders_2(A_83,D_125,C_119)
      | ~ r1_orders_2(A_83,D_125,B_107)
      | ~ m1_subset_1(D_125,u1_struct_0(A_83))
      | ~ m1_subset_1(C_119,u1_struct_0(A_83))
      | ~ m1_subset_1(B_107,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83)
      | ~ v2_lattice3(A_83)
      | ~ v5_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2164,plain,(
    ! [A_345,B_346,C_347] :
      ( k11_lattice3(A_345,B_346,C_347) = B_346
      | ~ r1_orders_2(A_345,B_346,C_347)
      | ~ r1_orders_2(A_345,B_346,B_346)
      | ~ m1_subset_1(C_347,u1_struct_0(A_345))
      | ~ m1_subset_1(B_346,u1_struct_0(A_345))
      | ~ l1_orders_2(A_345)
      | ~ v2_lattice3(A_345)
      | ~ v5_orders_2(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_54,c_1633])).

tff(c_2166,plain,(
    ! [E_341] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341) = k10_lattice3('#skF_4','#skF_5','#skF_5')
      | ~ r1_orders_2('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),k10_lattice3('#skF_4','#skF_5','#skF_5'))
      | ~ m1_subset_1(k10_lattice3('#skF_4','#skF_5','#skF_5'),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2027,c_2164])).

tff(c_2191,plain,(
    ! [E_341] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341) = k10_lattice3('#skF_4','#skF_5','#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_1831,c_1966,c_2166])).

tff(c_2192,plain,(
    ! [E_341] :
      ( k11_lattice3('#skF_4',k10_lattice3('#skF_4','#skF_5','#skF_5'),E_341) = k10_lattice3('#skF_4','#skF_5','#skF_5')
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_2191])).

tff(c_2630,plain,(
    ! [E_341] :
      ( k11_lattice3('#skF_4','#skF_5',E_341) = '#skF_5'
      | ~ r1_orders_2('#skF_4','#skF_5',E_341)
      | ~ m1_subset_1(E_341,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_2624,c_2192])).

tff(c_3934,plain,
    ( k11_lattice3('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ r1_orders_2('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_3881,c_2630])).

tff(c_4070,plain,(
    ~ r1_orders_2('#skF_4','#skF_5',k10_lattice3('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1545,c_3934])).

tff(c_4136,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_4070])).

tff(c_4139,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_4136])).

tff(c_4141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_4139])).

tff(c_4142,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_4147,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4142,c_14])).

tff(c_4152,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4147])).

tff(c_4155,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4152])).

tff(c_4159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4155])).

tff(c_4160,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4147])).

tff(c_4166,plain,
    ( ~ v2_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_4160,c_30])).

tff(c_4173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.63  
% 7.67/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.63  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_relat_1 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k11_lattice3 > k10_lattice3 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 7.67/2.63  
% 7.67/2.63  %Foreground sorts:
% 7.67/2.63  
% 7.67/2.63  
% 7.67/2.63  %Background operators:
% 7.67/2.63  
% 7.67/2.63  
% 7.67/2.63  %Foreground operators:
% 7.67/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.67/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.67/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/2.63  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 7.67/2.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.67/2.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.67/2.63  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 7.67/2.63  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 7.67/2.63  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 7.67/2.63  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 7.67/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.67/2.63  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 7.67/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.67/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.67/2.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.67/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.67/2.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.67/2.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.67/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.67/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.67/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.67/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.63  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 7.67/2.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.67/2.63  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 7.67/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.67/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.67/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.67/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.67/2.63  
% 7.67/2.66  tff(f_227, negated_conjecture, ~(![A]: (((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k12_lattice3(A, B, k13_lattice3(A, B, C)) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_lattice3)).
% 7.67/2.66  tff(f_80, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.67/2.66  tff(f_184, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 7.67/2.66  tff(f_118, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 7.67/2.66  tff(f_196, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 7.67/2.66  tff(f_98, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 7.67/2.66  tff(f_151, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 7.67/2.66  tff(f_110, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k12_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 7.67/2.66  tff(f_208, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 7.67/2.66  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.67/2.66  tff(f_84, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 7.67/2.66  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.67/2.66  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 7.67/2.66  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.67/2.66  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 7.67/2.66  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 7.67/2.66  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.67/2.66  tff(c_74, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_76, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_24, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.67/2.66  tff(c_80, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_745, plain, (![A_235, B_236, C_237, D_238]: (m1_subset_1('#skF_3'(A_235, B_236, C_237, D_238), u1_struct_0(A_235)) | k11_lattice3(A_235, B_236, C_237)=D_238 | ~r1_orders_2(A_235, D_238, C_237) | ~r1_orders_2(A_235, D_238, B_236) | ~m1_subset_1(D_238, u1_struct_0(A_235)) | ~m1_subset_1(C_237, u1_struct_0(A_235)) | ~m1_subset_1(B_236, u1_struct_0(A_235)) | ~l1_orders_2(A_235) | ~v2_lattice3(A_235) | ~v5_orders_2(A_235) | v2_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.67/2.66  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_34, plain, (![A_34, B_35, C_36]: (m1_subset_1(k10_lattice3(A_34, B_35, C_36), u1_struct_0(A_34)) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.67/2.66  tff(c_72, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_309, plain, (![A_191, B_192, C_193]: (k12_lattice3(A_191, B_192, C_193)=k11_lattice3(A_191, B_192, C_193) | ~m1_subset_1(C_193, u1_struct_0(A_191)) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_orders_2(A_191) | ~v2_lattice3(A_191) | ~v5_orders_2(A_191))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.67/2.66  tff(c_313, plain, (![B_192]: (k12_lattice3('#skF_4', B_192, '#skF_5')=k11_lattice3('#skF_4', B_192, '#skF_5') | ~m1_subset_1(B_192, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_309])).
% 7.67/2.66  tff(c_373, plain, (![B_198]: (k12_lattice3('#skF_4', B_198, '#skF_5')=k11_lattice3('#skF_4', B_198, '#skF_5') | ~m1_subset_1(B_198, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_313])).
% 7.67/2.66  tff(c_377, plain, (![B_35, C_36]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_5') | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_373])).
% 7.67/2.66  tff(c_630, plain, (![B_223, C_224]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_223, C_224), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_223, C_224), '#skF_5') | ~m1_subset_1(C_224, u1_struct_0('#skF_4')) | ~m1_subset_1(B_223, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_377])).
% 7.67/2.66  tff(c_642, plain, (![B_223]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_223, '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_223, '#skF_6'), '#skF_5') | ~m1_subset_1(B_223, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_630])).
% 7.67/2.66  tff(c_760, plain, (![B_236, C_237, D_238]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_3'('#skF_4', B_236, C_237, D_238), '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_3'('#skF_4', B_236, C_237, D_238), '#skF_6'), '#skF_5') | k11_lattice3('#skF_4', B_236, C_237)=D_238 | ~r1_orders_2('#skF_4', D_238, C_237) | ~r1_orders_2('#skF_4', D_238, B_236) | ~m1_subset_1(D_238, u1_struct_0('#skF_4')) | ~m1_subset_1(C_237, u1_struct_0('#skF_4')) | ~m1_subset_1(B_236, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_745, c_642])).
% 7.67/2.66  tff(c_844, plain, (![B_236, C_237, D_238]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_3'('#skF_4', B_236, C_237, D_238), '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_3'('#skF_4', B_236, C_237, D_238), '#skF_6'), '#skF_5') | k11_lattice3('#skF_4', B_236, C_237)=D_238 | ~r1_orders_2('#skF_4', D_238, C_237) | ~r1_orders_2('#skF_4', D_238, B_236) | ~m1_subset_1(D_238, u1_struct_0('#skF_4')) | ~m1_subset_1(C_237, u1_struct_0('#skF_4')) | ~m1_subset_1(B_236, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_760])).
% 7.67/2.66  tff(c_1316, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_844])).
% 7.67/2.66  tff(c_30, plain, (![A_30]: (~v2_struct_0(A_30) | ~v2_lattice3(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.67/2.66  tff(c_1319, plain, (~v2_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_1316, c_30])).
% 7.67/2.66  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_1319])).
% 7.67/2.66  tff(c_1328, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_844])).
% 7.67/2.66  tff(c_78, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_427, plain, (![A_200, B_201, C_202]: (r1_orders_2(A_200, B_201, k10_lattice3(A_200, B_201, C_202)) | ~m1_subset_1(k10_lattice3(A_200, B_201, C_202), u1_struct_0(A_200)) | ~m1_subset_1(C_202, u1_struct_0(A_200)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~v1_lattice3(A_200) | ~v5_orders_2(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.67/2.66  tff(c_430, plain, (![A_34, B_35, C_36]: (r1_orders_2(A_34, B_35, k10_lattice3(A_34, B_35, C_36)) | ~v1_lattice3(A_34) | ~v5_orders_2(A_34) | v2_struct_0(A_34) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_34, c_427])).
% 7.67/2.66  tff(c_1349, plain, (![A_307, B_308, B_309, C_310]: (k12_lattice3(A_307, B_308, k10_lattice3(A_307, B_309, C_310))=k11_lattice3(A_307, B_308, k10_lattice3(A_307, B_309, C_310)) | ~m1_subset_1(B_308, u1_struct_0(A_307)) | ~v2_lattice3(A_307) | ~v5_orders_2(A_307) | ~m1_subset_1(C_310, u1_struct_0(A_307)) | ~m1_subset_1(B_309, u1_struct_0(A_307)) | ~l1_orders_2(A_307))), inference(resolution, [status(thm)], [c_34, c_309])).
% 7.67/2.66  tff(c_1357, plain, (![B_309, C_310]: (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_309, C_310))=k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_309, C_310)) | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~m1_subset_1(C_310, u1_struct_0('#skF_4')) | ~m1_subset_1(B_309, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_1349])).
% 7.67/2.66  tff(c_1369, plain, (![B_311, C_312]: (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_311, C_312))=k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_311, C_312)) | ~m1_subset_1(C_312, u1_struct_0('#skF_4')) | ~m1_subset_1(B_311, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_76, c_1357])).
% 7.67/2.66  tff(c_1444, plain, (![B_318]: (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_318, '#skF_6'))=k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_318, '#skF_6')) | ~m1_subset_1(B_318, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_1369])).
% 7.67/2.66  tff(c_1474, plain, (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))=k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_1444])).
% 7.67/2.66  tff(c_668, plain, (![B_230]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_230, '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_230, '#skF_6'), '#skF_5') | ~m1_subset_1(B_230, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_630])).
% 7.67/2.66  tff(c_682, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_72, c_668])).
% 7.67/2.66  tff(c_228, plain, (![A_184, C_185, B_186]: (k12_lattice3(A_184, C_185, B_186)=k12_lattice3(A_184, B_186, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_184)) | ~m1_subset_1(B_186, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v2_lattice3(A_184) | ~v5_orders_2(A_184))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.67/2.66  tff(c_232, plain, (![B_186]: (k12_lattice3('#skF_4', B_186, '#skF_5')=k12_lattice3('#skF_4', '#skF_5', B_186) | ~m1_subset_1(B_186, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_228])).
% 7.67/2.66  tff(c_246, plain, (![B_187]: (k12_lattice3('#skF_4', B_187, '#skF_5')=k12_lattice3('#skF_4', '#skF_5', B_187) | ~m1_subset_1(B_187, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_232])).
% 7.67/2.66  tff(c_250, plain, (![B_35, C_36]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_5')=k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_246])).
% 7.67/2.66  tff(c_908, plain, (![B_239, C_240]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_239, C_240), '#skF_5')=k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_239, C_240)) | ~m1_subset_1(C_240, u1_struct_0('#skF_4')) | ~m1_subset_1(B_239, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_250])).
% 7.67/2.66  tff(c_960, plain, (![B_242]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_242, '#skF_6'), '#skF_5')=k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', B_242, '#skF_6')) | ~m1_subset_1(B_242, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_908])).
% 7.67/2.66  tff(c_971, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')=k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_960])).
% 7.67/2.66  tff(c_982, plain, (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_682, c_971])).
% 7.67/2.66  tff(c_1506, plain, (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')=k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_982])).
% 7.67/2.66  tff(c_169, plain, (![A_179, B_180, C_181]: (k13_lattice3(A_179, B_180, C_181)=k10_lattice3(A_179, B_180, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179) | ~v1_lattice3(A_179) | ~v5_orders_2(A_179))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.67/2.66  tff(c_175, plain, (![B_180]: (k13_lattice3('#skF_4', B_180, '#skF_6')=k10_lattice3('#skF_4', B_180, '#skF_6') | ~m1_subset_1(B_180, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_169])).
% 7.67/2.66  tff(c_207, plain, (![B_183]: (k13_lattice3('#skF_4', B_183, '#skF_6')=k10_lattice3('#skF_4', B_183, '#skF_6') | ~m1_subset_1(B_183, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_175])).
% 7.67/2.66  tff(c_221, plain, (k13_lattice3('#skF_4', '#skF_5', '#skF_6')=k10_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_207])).
% 7.67/2.66  tff(c_68, plain, (k12_lattice3('#skF_4', '#skF_5', k13_lattice3('#skF_4', '#skF_5', '#skF_6'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_223, plain, (k12_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_68])).
% 7.67/2.66  tff(c_985, plain, (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_982, c_223])).
% 7.67/2.66  tff(c_1545, plain, (k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_985])).
% 7.67/2.66  tff(c_369, plain, (![A_195, C_196, B_197]: (r1_orders_2(A_195, C_196, k10_lattice3(A_195, B_197, C_196)) | ~m1_subset_1(k10_lattice3(A_195, B_197, C_196), u1_struct_0(A_195)) | ~m1_subset_1(C_196, u1_struct_0(A_195)) | ~m1_subset_1(B_197, u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v1_lattice3(A_195) | ~v5_orders_2(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.67/2.66  tff(c_372, plain, (![A_34, C_36, B_35]: (r1_orders_2(A_34, C_36, k10_lattice3(A_34, B_35, C_36)) | ~v1_lattice3(A_34) | ~v5_orders_2(A_34) | v2_struct_0(A_34) | ~m1_subset_1(C_36, u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_34, c_369])).
% 7.67/2.66  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.67/2.66  tff(c_97, plain, (![A_153]: (m1_subset_1(u1_orders_2(A_153), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153), u1_struct_0(A_153)))) | ~l1_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.67/2.66  tff(c_4, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.67/2.66  tff(c_100, plain, (![A_153]: (v1_relat_1(u1_orders_2(A_153)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_153), u1_struct_0(A_153))) | ~l1_orders_2(A_153))), inference(resolution, [status(thm)], [c_97, c_4])).
% 7.67/2.66  tff(c_103, plain, (![A_153]: (v1_relat_1(u1_orders_2(A_153)) | ~l1_orders_2(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_100])).
% 7.67/2.66  tff(c_82, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 7.67/2.66  tff(c_18, plain, (![A_19]: (r1_relat_2(u1_orders_2(A_19), u1_struct_0(A_19)) | ~v3_orders_2(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.67/2.66  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.67/2.66  tff(c_104, plain, (![C_154, A_155, B_156]: (r2_hidden(k4_tarski(C_154, C_154), A_155) | ~r2_hidden(C_154, B_156) | ~r1_relat_2(A_155, B_156) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.67/2.66  tff(c_118, plain, (![A_160, A_161, B_162]: (r2_hidden(k4_tarski(A_160, A_160), A_161) | ~r1_relat_2(A_161, B_162) | ~v1_relat_1(A_161) | v1_xboole_0(B_162) | ~m1_subset_1(A_160, B_162))), inference(resolution, [status(thm)], [c_2, c_104])).
% 7.67/2.66  tff(c_156, plain, (![A_177, A_178]: (r2_hidden(k4_tarski(A_177, A_177), u1_orders_2(A_178)) | ~v1_relat_1(u1_orders_2(A_178)) | v1_xboole_0(u1_struct_0(A_178)) | ~m1_subset_1(A_177, u1_struct_0(A_178)) | ~v3_orders_2(A_178) | ~l1_orders_2(A_178))), inference(resolution, [status(thm)], [c_18, c_118])).
% 7.67/2.66  tff(c_20, plain, (![A_20, B_24, C_26]: (r1_orders_2(A_20, B_24, C_26) | ~r2_hidden(k4_tarski(B_24, C_26), u1_orders_2(A_20)) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.67/2.66  tff(c_285, plain, (![A_189, A_190]: (r1_orders_2(A_189, A_190, A_190) | ~v1_relat_1(u1_orders_2(A_189)) | v1_xboole_0(u1_struct_0(A_189)) | ~m1_subset_1(A_190, u1_struct_0(A_189)) | ~v3_orders_2(A_189) | ~l1_orders_2(A_189))), inference(resolution, [status(thm)], [c_156, c_20])).
% 7.67/2.66  tff(c_289, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v3_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_72, c_285])).
% 7.67/2.66  tff(c_295, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_82, c_289])).
% 7.67/2.66  tff(c_299, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_295])).
% 7.67/2.66  tff(c_302, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_103, c_299])).
% 7.67/2.66  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_302])).
% 7.67/2.66  tff(c_308, plain, (v1_relat_1(u1_orders_2('#skF_4'))), inference(splitRight, [status(thm)], [c_295])).
% 7.67/2.66  tff(c_291, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_6') | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v3_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_70, c_285])).
% 7.67/2.66  tff(c_298, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_6') | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_82, c_291])).
% 7.67/2.66  tff(c_325, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_298])).
% 7.67/2.66  tff(c_326, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_325])).
% 7.67/2.66  tff(c_14, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.67/2.66  tff(c_346, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_326, c_14])).
% 7.67/2.66  tff(c_347, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_346])).
% 7.67/2.66  tff(c_350, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_347])).
% 7.67/2.66  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_350])).
% 7.67/2.66  tff(c_355, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_346])).
% 7.67/2.66  tff(c_359, plain, (~v2_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_355, c_30])).
% 7.67/2.66  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_359])).
% 7.67/2.66  tff(c_367, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_325])).
% 7.67/2.66  tff(c_52, plain, (![A_83, B_107, C_119, D_125]: (r1_orders_2(A_83, '#skF_3'(A_83, B_107, C_119, D_125), C_119) | k11_lattice3(A_83, B_107, C_119)=D_125 | ~r1_orders_2(A_83, D_125, C_119) | ~r1_orders_2(A_83, D_125, B_107) | ~m1_subset_1(D_125, u1_struct_0(A_83)) | ~m1_subset_1(C_119, u1_struct_0(A_83)) | ~m1_subset_1(B_107, u1_struct_0(A_83)) | ~l1_orders_2(A_83) | ~v2_lattice3(A_83) | ~v5_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.67/2.66  tff(c_1633, plain, (![A_326, B_327, C_328, D_329]: (~r1_orders_2(A_326, '#skF_3'(A_326, B_327, C_328, D_329), D_329) | k11_lattice3(A_326, B_327, C_328)=D_329 | ~r1_orders_2(A_326, D_329, C_328) | ~r1_orders_2(A_326, D_329, B_327) | ~m1_subset_1(D_329, u1_struct_0(A_326)) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~m1_subset_1(B_327, u1_struct_0(A_326)) | ~l1_orders_2(A_326) | ~v2_lattice3(A_326) | ~v5_orders_2(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.67/2.66  tff(c_2810, plain, (![A_357, B_358, C_359]: (k11_lattice3(A_357, B_358, C_359)=C_359 | ~r1_orders_2(A_357, C_359, C_359) | ~r1_orders_2(A_357, C_359, B_358) | ~m1_subset_1(C_359, u1_struct_0(A_357)) | ~m1_subset_1(B_358, u1_struct_0(A_357)) | ~l1_orders_2(A_357) | ~v2_lattice3(A_357) | ~v5_orders_2(A_357) | v2_struct_0(A_357))), inference(resolution, [status(thm)], [c_52, c_1633])).
% 7.67/2.66  tff(c_2816, plain, (![B_358]: (k11_lattice3('#skF_4', B_358, '#skF_6')='#skF_6' | ~r1_orders_2('#skF_4', '#skF_6', B_358) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_358, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_367, c_2810])).
% 7.67/2.66  tff(c_2823, plain, (![B_358]: (k11_lattice3('#skF_4', B_358, '#skF_6')='#skF_6' | ~r1_orders_2('#skF_4', '#skF_6', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2816])).
% 7.67/2.67  tff(c_2829, plain, (![B_360]: (k11_lattice3('#skF_4', B_360, '#skF_6')='#skF_6' | ~r1_orders_2('#skF_4', '#skF_6', B_360) | ~m1_subset_1(B_360, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1328, c_2823])).
% 7.67/2.67  tff(c_2841, plain, (![B_35, C_36]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_6')='#skF_6' | ~r1_orders_2('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2829])).
% 7.67/2.67  tff(c_3284, plain, (![B_390, C_391]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_390, C_391), '#skF_6')='#skF_6' | ~r1_orders_2('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_390, C_391)) | ~m1_subset_1(C_391, u1_struct_0('#skF_4')) | ~m1_subset_1(B_390, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2841])).
% 7.67/2.67  tff(c_3298, plain, (![B_35]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, '#skF_6'), '#skF_6')='#skF_6' | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_372, c_3284])).
% 7.67/2.67  tff(c_3309, plain, (![B_35]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, '#skF_6'), '#skF_6')='#skF_6' | v2_struct_0('#skF_4') | ~m1_subset_1(B_35, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_80, c_78, c_3298])).
% 7.67/2.67  tff(c_3394, plain, (![B_393]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_393, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_393, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1328, c_3309])).
% 7.67/2.67  tff(c_3424, plain, (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_72, c_3394])).
% 7.67/2.67  tff(c_1359, plain, (![B_309, C_310]: (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_309, C_310))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_309, C_310)) | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~m1_subset_1(C_310, u1_struct_0('#skF_4')) | ~m1_subset_1(B_309, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1349])).
% 7.67/2.67  tff(c_1569, plain, (![B_323, C_324]: (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_323, C_324))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_323, C_324)) | ~m1_subset_1(C_324, u1_struct_0('#skF_4')) | ~m1_subset_1(B_323, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_76, c_1359])).
% 7.67/2.67  tff(c_1679, plain, (![B_330]: (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_330, '#skF_6'))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_330, '#skF_6')) | ~m1_subset_1(B_330, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_1569])).
% 7.67/2.67  tff(c_1709, plain, (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_1679])).
% 7.67/2.67  tff(c_315, plain, (![B_192]: (k12_lattice3('#skF_4', B_192, '#skF_6')=k11_lattice3('#skF_4', B_192, '#skF_6') | ~m1_subset_1(B_192, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_309])).
% 7.67/2.67  tff(c_402, plain, (![B_199]: (k12_lattice3('#skF_4', B_199, '#skF_6')=k11_lattice3('#skF_4', B_199, '#skF_6') | ~m1_subset_1(B_199, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_315])).
% 7.67/2.67  tff(c_406, plain, (![B_35, C_36]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_6') | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_402])).
% 7.67/2.67  tff(c_432, plain, (![B_205, C_206]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_205, C_206), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_205, C_206), '#skF_6') | ~m1_subset_1(C_206, u1_struct_0('#skF_4')) | ~m1_subset_1(B_205, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_406])).
% 7.67/2.67  tff(c_469, plain, (![B_208]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_208, '#skF_6'), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_208, '#skF_6'), '#skF_6') | ~m1_subset_1(B_208, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_432])).
% 7.67/2.67  tff(c_483, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_72, c_469])).
% 7.67/2.67  tff(c_234, plain, (![B_186]: (k12_lattice3('#skF_4', B_186, '#skF_6')=k12_lattice3('#skF_4', '#skF_6', B_186) | ~m1_subset_1(B_186, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_228])).
% 7.67/2.67  tff(c_267, plain, (![B_188]: (k12_lattice3('#skF_4', B_188, '#skF_6')=k12_lattice3('#skF_4', '#skF_6', B_188) | ~m1_subset_1(B_188, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_234])).
% 7.67/2.67  tff(c_271, plain, (![B_35, C_36]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_35, C_36), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_35, C_36)) | ~m1_subset_1(C_36, u1_struct_0('#skF_4')) | ~m1_subset_1(B_35, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_267])).
% 7.67/2.67  tff(c_560, plain, (![B_216, C_217]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_216, C_217), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_216, C_217)) | ~m1_subset_1(C_217, u1_struct_0('#skF_4')) | ~m1_subset_1(B_216, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_271])).
% 7.67/2.67  tff(c_604, plain, (![B_222]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_222, '#skF_6'), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_222, '#skF_6')) | ~m1_subset_1(B_222, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_560])).
% 7.67/2.67  tff(c_611, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_604])).
% 7.67/2.67  tff(c_619, plain, (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_611])).
% 7.67/2.67  tff(c_1719, plain, (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_6'), '#skF_6')=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_619])).
% 7.67/2.67  tff(c_3427, plain, (k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_1719])).
% 7.67/2.67  tff(c_60, plain, (![A_83, B_107, C_119]: (r1_orders_2(A_83, k11_lattice3(A_83, B_107, C_119), C_119) | ~m1_subset_1(k11_lattice3(A_83, B_107, C_119), u1_struct_0(A_83)) | ~m1_subset_1(C_119, u1_struct_0(A_83)) | ~m1_subset_1(B_107, u1_struct_0(A_83)) | ~l1_orders_2(A_83) | ~v2_lattice3(A_83) | ~v5_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.67/2.67  tff(c_3477, plain, (r1_orders_2('#skF_4', k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6')), k10_lattice3('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3427, c_60])).
% 7.67/2.67  tff(c_3487, plain, (r1_orders_2('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_70, c_3427, c_3477])).
% 7.67/2.67  tff(c_3488, plain, (r1_orders_2('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1328, c_3487])).
% 7.67/2.67  tff(c_3847, plain, (~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_3488])).
% 7.67/2.67  tff(c_3875, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_34, c_3847])).
% 7.67/2.67  tff(c_3879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3875])).
% 7.67/2.67  tff(c_3881, plain, (m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3488])).
% 7.67/2.67  tff(c_307, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_295])).
% 7.67/2.67  tff(c_323, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_307])).
% 7.67/2.67  tff(c_1396, plain, (![A_313, B_314, C_315, D_316]: (r1_orders_2(A_313, B_314, '#skF_2'(A_313, B_314, C_315, D_316)) | k10_lattice3(A_313, B_314, C_315)=D_316 | ~r1_orders_2(A_313, C_315, D_316) | ~r1_orders_2(A_313, B_314, D_316) | ~m1_subset_1(D_316, u1_struct_0(A_313)) | ~m1_subset_1(C_315, u1_struct_0(A_313)) | ~m1_subset_1(B_314, u1_struct_0(A_313)) | ~l1_orders_2(A_313) | ~v1_lattice3(A_313) | ~v5_orders_2(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.67/2.67  tff(c_36, plain, (![A_37, D_79, B_61, C_73]: (~r1_orders_2(A_37, D_79, '#skF_2'(A_37, B_61, C_73, D_79)) | k10_lattice3(A_37, B_61, C_73)=D_79 | ~r1_orders_2(A_37, C_73, D_79) | ~r1_orders_2(A_37, B_61, D_79) | ~m1_subset_1(D_79, u1_struct_0(A_37)) | ~m1_subset_1(C_73, u1_struct_0(A_37)) | ~m1_subset_1(B_61, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v1_lattice3(A_37) | ~v5_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.67/2.67  tff(c_2570, plain, (![A_353, D_354, C_355]: (k10_lattice3(A_353, D_354, C_355)=D_354 | ~r1_orders_2(A_353, C_355, D_354) | ~r1_orders_2(A_353, D_354, D_354) | ~m1_subset_1(C_355, u1_struct_0(A_353)) | ~m1_subset_1(D_354, u1_struct_0(A_353)) | ~l1_orders_2(A_353) | ~v1_lattice3(A_353) | ~v5_orders_2(A_353) | v2_struct_0(A_353))), inference(resolution, [status(thm)], [c_1396, c_36])).
% 7.67/2.67  tff(c_2596, plain, (k10_lattice3('#skF_4', '#skF_5', '#skF_5')='#skF_5' | ~r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_323, c_2570])).
% 7.67/2.67  tff(c_2623, plain, (k10_lattice3('#skF_4', '#skF_5', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_323, c_2596])).
% 7.67/2.67  tff(c_2624, plain, (k10_lattice3('#skF_4', '#skF_5', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1328, c_2623])).
% 7.67/2.67  tff(c_1596, plain, (![B_325]: (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_325, '#skF_5'))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_325, '#skF_5')) | ~m1_subset_1(B_325, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_72, c_1569])).
% 7.67/2.67  tff(c_1626, plain, (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5'))=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1596])).
% 7.67/2.67  tff(c_445, plain, (![B_207]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_207, '#skF_5'), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', B_207, '#skF_5'), '#skF_6') | ~m1_subset_1(B_207, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_72, c_432])).
% 7.67/2.67  tff(c_459, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6')=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_72, c_445])).
% 7.67/2.67  tff(c_578, plain, (![B_221]: (k12_lattice3('#skF_4', k10_lattice3('#skF_4', B_221, '#skF_5'), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', B_221, '#skF_5')) | ~m1_subset_1(B_221, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_72, c_560])).
% 7.67/2.67  tff(c_585, plain, (k12_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6')=k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_578])).
% 7.67/2.67  tff(c_593, plain, (k12_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5'))=k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_585])).
% 7.67/2.67  tff(c_1628, plain, (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6')=k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_593])).
% 7.67/2.67  tff(c_1654, plain, (r1_orders_2('#skF_4', k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), '#skF_6'), '#skF_6') | ~m1_subset_1(k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5')), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1628, c_60])).
% 7.67/2.67  tff(c_1661, plain, (r1_orders_2('#skF_4', k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5')), '#skF_6') | ~m1_subset_1(k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5')), u1_struct_0('#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1628, c_1654])).
% 7.67/2.67  tff(c_1662, plain, (r1_orders_2('#skF_4', k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5')), '#skF_6') | ~m1_subset_1(k11_lattice3('#skF_4', '#skF_6', k10_lattice3('#skF_4', '#skF_5', '#skF_5')), u1_struct_0('#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1328, c_1661])).
% 7.67/2.67  tff(c_1822, plain, (~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1662])).
% 7.67/2.67  tff(c_1825, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1822])).
% 7.67/2.67  tff(c_1829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1825])).
% 7.67/2.67  tff(c_1831, plain, (m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1662])).
% 7.67/2.67  tff(c_368, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_325])).
% 7.67/2.67  tff(c_166, plain, (![A_178, A_177]: (r1_orders_2(A_178, A_177, A_177) | ~v1_relat_1(u1_orders_2(A_178)) | v1_xboole_0(u1_struct_0(A_178)) | ~m1_subset_1(A_177, u1_struct_0(A_178)) | ~v3_orders_2(A_178) | ~l1_orders_2(A_178))), inference(resolution, [status(thm)], [c_156, c_20])).
% 7.67/2.67  tff(c_1909, plain, (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), k10_lattice3('#skF_4', '#skF_5', '#skF_5')) | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v3_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_1831, c_166])).
% 7.67/2.67  tff(c_1965, plain, (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), k10_lattice3('#skF_4', '#skF_5', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_82, c_308, c_1909])).
% 7.67/2.67  tff(c_1966, plain, (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), k10_lattice3('#skF_4', '#skF_5', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_368, c_1965])).
% 7.67/2.67  tff(c_2019, plain, (![A_338, B_339, C_340, E_341]: (r1_orders_2(A_338, k10_lattice3(A_338, B_339, C_340), E_341) | ~r1_orders_2(A_338, C_340, E_341) | ~r1_orders_2(A_338, B_339, E_341) | ~m1_subset_1(E_341, u1_struct_0(A_338)) | ~m1_subset_1(k10_lattice3(A_338, B_339, C_340), u1_struct_0(A_338)) | ~m1_subset_1(C_340, u1_struct_0(A_338)) | ~m1_subset_1(B_339, u1_struct_0(A_338)) | ~l1_orders_2(A_338) | ~v1_lattice3(A_338) | ~v5_orders_2(A_338) | v2_struct_0(A_338))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.67/2.67  tff(c_2021, plain, (![E_341]: (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341) | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1831, c_2019])).
% 7.67/2.67  tff(c_2026, plain, (![E_341]: (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341) | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_2021])).
% 7.67/2.67  tff(c_2027, plain, (![E_341]: (r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341) | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1328, c_2026])).
% 7.67/2.67  tff(c_54, plain, (![A_83, B_107, C_119, D_125]: (r1_orders_2(A_83, '#skF_3'(A_83, B_107, C_119, D_125), B_107) | k11_lattice3(A_83, B_107, C_119)=D_125 | ~r1_orders_2(A_83, D_125, C_119) | ~r1_orders_2(A_83, D_125, B_107) | ~m1_subset_1(D_125, u1_struct_0(A_83)) | ~m1_subset_1(C_119, u1_struct_0(A_83)) | ~m1_subset_1(B_107, u1_struct_0(A_83)) | ~l1_orders_2(A_83) | ~v2_lattice3(A_83) | ~v5_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.67/2.67  tff(c_2164, plain, (![A_345, B_346, C_347]: (k11_lattice3(A_345, B_346, C_347)=B_346 | ~r1_orders_2(A_345, B_346, C_347) | ~r1_orders_2(A_345, B_346, B_346) | ~m1_subset_1(C_347, u1_struct_0(A_345)) | ~m1_subset_1(B_346, u1_struct_0(A_345)) | ~l1_orders_2(A_345) | ~v2_lattice3(A_345) | ~v5_orders_2(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_54, c_1633])).
% 7.67/2.67  tff(c_2166, plain, (![E_341]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341)=k10_lattice3('#skF_4', '#skF_5', '#skF_5') | ~r1_orders_2('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), k10_lattice3('#skF_4', '#skF_5', '#skF_5')) | ~m1_subset_1(k10_lattice3('#skF_4', '#skF_5', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2027, c_2164])).
% 7.67/2.67  tff(c_2191, plain, (![E_341]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341)=k10_lattice3('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4') | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_1831, c_1966, c_2166])).
% 7.67/2.67  tff(c_2192, plain, (![E_341]: (k11_lattice3('#skF_4', k10_lattice3('#skF_4', '#skF_5', '#skF_5'), E_341)=k10_lattice3('#skF_4', '#skF_5', '#skF_5') | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1328, c_2191])).
% 7.67/2.67  tff(c_2630, plain, (![E_341]: (k11_lattice3('#skF_4', '#skF_5', E_341)='#skF_5' | ~r1_orders_2('#skF_4', '#skF_5', E_341) | ~m1_subset_1(E_341, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_2624, c_2192])).
% 7.67/2.67  tff(c_3934, plain, (k11_lattice3('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~r1_orders_2('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_3881, c_2630])).
% 7.67/2.67  tff(c_4070, plain, (~r1_orders_2('#skF_4', '#skF_5', k10_lattice3('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1545, c_3934])).
% 7.67/2.67  tff(c_4136, plain, (~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_430, c_4070])).
% 7.67/2.67  tff(c_4139, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_4136])).
% 7.67/2.67  tff(c_4141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1328, c_4139])).
% 7.67/2.67  tff(c_4142, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_307])).
% 7.67/2.67  tff(c_4147, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4142, c_14])).
% 7.67/2.67  tff(c_4152, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4147])).
% 7.67/2.67  tff(c_4155, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4152])).
% 7.67/2.67  tff(c_4159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4155])).
% 7.67/2.67  tff(c_4160, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_4147])).
% 7.67/2.67  tff(c_4166, plain, (~v2_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_4160, c_30])).
% 7.67/2.67  tff(c_4173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4166])).
% 7.67/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.67  
% 7.67/2.67  Inference rules
% 7.67/2.67  ----------------------
% 7.67/2.67  #Ref     : 0
% 7.67/2.67  #Sup     : 869
% 7.67/2.67  #Fact    : 0
% 7.67/2.67  #Define  : 0
% 7.67/2.67  #Split   : 13
% 7.67/2.67  #Chain   : 0
% 7.67/2.67  #Close   : 0
% 7.67/2.67  
% 7.67/2.67  Ordering : KBO
% 7.67/2.67  
% 7.67/2.67  Simplification rules
% 7.67/2.67  ----------------------
% 7.67/2.67  #Subsume      : 21
% 7.67/2.67  #Demod        : 1599
% 7.67/2.67  #Tautology    : 376
% 7.67/2.67  #SimpNegUnit  : 168
% 7.67/2.67  #BackRed      : 61
% 7.67/2.67  
% 7.67/2.67  #Partial instantiations: 0
% 7.67/2.67  #Strategies tried      : 1
% 7.67/2.67  
% 7.67/2.67  Timing (in seconds)
% 7.67/2.67  ----------------------
% 7.67/2.67  Preprocessing        : 0.40
% 7.67/2.67  Parsing              : 0.20
% 7.67/2.67  CNF conversion       : 0.04
% 7.67/2.67  Main loop            : 1.46
% 7.67/2.67  Inferencing          : 0.48
% 7.67/2.67  Reduction            : 0.51
% 7.67/2.67  Demodulation         : 0.37
% 7.67/2.67  BG Simplification    : 0.07
% 7.67/2.67  Subsumption          : 0.29
% 7.67/2.67  Abstraction          : 0.08
% 7.67/2.67  MUC search           : 0.00
% 7.67/2.67  Cooper               : 0.00
% 7.67/2.67  Total                : 1.93
% 7.67/2.67  Index Insertion      : 0.00
% 7.67/2.67  Index Deletion       : 0.00
% 7.67/2.67  Index Matching       : 0.00
% 7.67/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
