%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:58 EST 2020

% Result     : Theorem 53.05s
% Output     : CNFRefutation 53.05s
% Verified   : 
% Statistics : Number of formulae       :  183 (1441 expanded)
%              Number of leaves         :   46 ( 477 expanded)
%              Depth                    :   22
%              Number of atoms          :  429 (5453 expanded)
%              Number of equality atoms :   50 ( 259 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_171,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [B_73] :
      ( ~ v1_subset_1(B_73,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_109,plain,(
    ! [B_17] :
      ( ~ v1_subset_1(B_17,B_17)
      | ~ r1_tarski(B_17,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_105])).

tff(c_112,plain,(
    ! [B_17] : ~ v1_subset_1(B_17,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_124,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_127,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_130,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_127])).

tff(c_86,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_131,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_86])).

tff(c_149,plain,(
    ! [B_82,A_83] :
      ( v1_subset_1(B_82,A_83)
      | B_82 = A_83
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_155,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_159,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_155])).

tff(c_96,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_138,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_138])).

tff(c_148,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_160,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_148])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_168,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_74,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_113,plain,(
    ! [A_74] :
      ( k1_yellow_0(A_74,k1_xboole_0) = k3_yellow_0(A_74)
      | ~ l1_orders_2(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_113])).

tff(c_132,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k1_yellow_0(A_78,B_79),u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_135,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_132])).

tff(c_137,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_135])).

tff(c_170,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_137])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_170])).

tff(c_177,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_216,plain,(
    ! [C_92,A_93,B_94] :
      ( r2_hidden(C_92,A_93)
      | ~ r2_hidden(C_92,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [A_95] :
      ( r2_hidden(k3_yellow_0('#skF_5'),A_95)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_177,c_216])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_259,plain,(
    ! [A_105,A_106] :
      ( r2_hidden(k3_yellow_0('#skF_5'),A_105)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_106)) ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_265,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_259])).

tff(c_304,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_307,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_313,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_55692,plain,(
    ! [A_2116,B_2117,C_2118] :
      ( m1_subset_1('#skF_1'(A_2116,B_2117,C_2118),A_2116)
      | C_2118 = B_2117
      | ~ m1_subset_1(C_2118,k1_zfmisc_1(A_2116))
      | ~ m1_subset_1(B_2117,k1_zfmisc_1(A_2116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_614,plain,(
    ! [A_152,A_153,B_154] :
      ( r2_hidden(A_152,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153))
      | v1_xboole_0(B_154)
      | ~ m1_subset_1(A_152,B_154) ) ),
    inference(resolution,[status(thm)],[c_20,c_216])).

tff(c_632,plain,(
    ! [A_152,B_17,A_16] :
      ( r2_hidden(A_152,B_17)
      | v1_xboole_0(A_16)
      | ~ m1_subset_1(A_152,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_614])).

tff(c_57408,plain,(
    ! [A_2350,B_2351,C_2352,B_2353] :
      ( r2_hidden('#skF_1'(A_2350,B_2351,C_2352),B_2353)
      | v1_xboole_0(A_2350)
      | ~ r1_tarski(A_2350,B_2353)
      | C_2352 = B_2351
      | ~ m1_subset_1(C_2352,k1_zfmisc_1(A_2350))
      | ~ m1_subset_1(B_2351,k1_zfmisc_1(A_2350)) ) ),
    inference(resolution,[status(thm)],[c_55692,c_632])).

tff(c_26,plain,(
    ! [A_18,C_20,B_19] :
      ( m1_subset_1(A_18,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_349,plain,(
    ! [A_18] :
      ( m1_subset_1(A_18,'#skF_6')
      | ~ r2_hidden(A_18,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_313,c_26])).

tff(c_57808,plain,(
    ! [A_2394,B_2395,C_2396] :
      ( m1_subset_1('#skF_1'(A_2394,B_2395,C_2396),'#skF_6')
      | v1_xboole_0(A_2394)
      | ~ r1_tarski(A_2394,'#skF_6')
      | C_2396 = B_2395
      | ~ m1_subset_1(C_2396,k1_zfmisc_1(A_2394))
      | ~ m1_subset_1(B_2395,k1_zfmisc_1(A_2394)) ) ),
    inference(resolution,[status(thm)],[c_57408,c_349])).

tff(c_619,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_152,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_313,c_614])).

tff(c_630,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,'#skF_6')
      | ~ m1_subset_1(A_152,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_619])).

tff(c_626,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_152,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_614])).

tff(c_635,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_152,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_626])).

tff(c_55992,plain,(
    ! [A_2161,B_2162,C_2163] :
      ( ~ r2_hidden('#skF_1'(A_2161,B_2162,C_2163),C_2163)
      | ~ r2_hidden('#skF_1'(A_2161,B_2162,C_2163),B_2162)
      | C_2163 = B_2162
      | ~ m1_subset_1(C_2163,k1_zfmisc_1(A_2161))
      | ~ m1_subset_1(B_2162,k1_zfmisc_1(A_2161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56251,plain,(
    ! [A_2198,B_2199] :
      ( ~ r2_hidden('#skF_1'(A_2198,B_2199,u1_struct_0('#skF_5')),B_2199)
      | u1_struct_0('#skF_5') = B_2199
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2198))
      | ~ m1_subset_1(B_2199,k1_zfmisc_1(A_2198))
      | ~ m1_subset_1('#skF_1'(A_2198,B_2199,u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_635,c_55992])).

tff(c_56289,plain,(
    ! [A_2198] :
      ( u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2198))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2198))
      | ~ m1_subset_1('#skF_1'(A_2198,'#skF_6',u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_630,c_56251])).

tff(c_56514,plain,(
    ! [A_2198] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2198))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2198))
      | ~ m1_subset_1('#skF_1'(A_2198,'#skF_6',u1_struct_0('#skF_5')),'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_56289])).

tff(c_57839,plain,(
    ! [A_2394] :
      ( v1_xboole_0(A_2394)
      | ~ r1_tarski(A_2394,'#skF_6')
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2394))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2394)) ) ),
    inference(resolution,[status(thm)],[c_57808,c_56514])).

tff(c_57844,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_57839])).

tff(c_10,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56023,plain,(
    ! [A_2164,B_2165] :
      ( ~ r2_hidden('#skF_1'(A_2164,B_2165,'#skF_6'),B_2165)
      | B_2165 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2164))
      | ~ m1_subset_1(B_2165,k1_zfmisc_1(A_2164))
      | ~ m1_subset_1('#skF_1'(A_2164,B_2165,'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_630,c_55992])).

tff(c_56058,plain,(
    ! [A_2164] :
      ( u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2164))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2164))
      | ~ m1_subset_1('#skF_1'(A_2164,u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_635,c_56023])).

tff(c_56156,plain,(
    ! [A_2185] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2185))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_2185))
      | ~ m1_subset_1('#skF_1'(A_2185,u1_struct_0('#skF_5'),'#skF_6'),'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_56058])).

tff(c_56160,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_56156])).

tff(c_56163,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_56160])).

tff(c_56164,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_56163])).

tff(c_57862,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57844,c_56164])).

tff(c_57892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_57862])).

tff(c_57894,plain,(
    u1_struct_0('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_57839])).

tff(c_48,plain,(
    ! [A_37,B_39] :
      ( r2_lattice3(A_37,k1_xboole_0,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_55737,plain,(
    ! [A_37,B_2117,C_2118] :
      ( r2_lattice3(A_37,k1_xboole_0,'#skF_1'(u1_struct_0(A_37),B_2117,C_2118))
      | ~ l1_orders_2(A_37)
      | C_2118 = B_2117
      | ~ m1_subset_1(C_2118,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_2117,k1_zfmisc_1(u1_struct_0(A_37))) ) ),
    inference(resolution,[status(thm)],[c_55692,c_48])).

tff(c_55932,plain,(
    ! [A_2151,B_2152,C_2153] :
      ( r2_hidden('#skF_1'(A_2151,B_2152,C_2153),B_2152)
      | r2_hidden('#skF_1'(A_2151,B_2152,C_2153),C_2153)
      | C_2153 = B_2152
      | ~ m1_subset_1(C_2153,k1_zfmisc_1(A_2151))
      | ~ m1_subset_1(B_2152,k1_zfmisc_1(A_2151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_238,plain,(
    ! [A_98,C_99,B_100] :
      ( m1_subset_1(A_98,C_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_99))
      | ~ r2_hidden(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_243,plain,(
    ! [A_98,B_17,A_16] :
      ( m1_subset_1(A_98,B_17)
      | ~ r2_hidden(A_98,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_238])).

tff(c_60803,plain,(
    ! [A_2584,B_2585,C_2586,B_2587] :
      ( m1_subset_1('#skF_1'(A_2584,B_2585,C_2586),B_2587)
      | ~ r1_tarski(C_2586,B_2587)
      | r2_hidden('#skF_1'(A_2584,B_2585,C_2586),B_2585)
      | C_2586 = B_2585
      | ~ m1_subset_1(C_2586,k1_zfmisc_1(A_2584))
      | ~ m1_subset_1(B_2585,k1_zfmisc_1(A_2584)) ) ),
    inference(resolution,[status(thm)],[c_55932,c_243])).

tff(c_84958,plain,(
    ! [B_3500,B_3503,C_3502,A_3501,B_3504] :
      ( m1_subset_1('#skF_1'(A_3501,B_3504,C_3502),B_3503)
      | ~ r1_tarski(B_3504,B_3503)
      | m1_subset_1('#skF_1'(A_3501,B_3504,C_3502),B_3500)
      | ~ r1_tarski(C_3502,B_3500)
      | C_3502 = B_3504
      | ~ m1_subset_1(C_3502,k1_zfmisc_1(A_3501))
      | ~ m1_subset_1(B_3504,k1_zfmisc_1(A_3501)) ) ),
    inference(resolution,[status(thm)],[c_60803,c_243])).

tff(c_85278,plain,(
    ! [A_3501,B_3500] :
      ( ~ r1_tarski('#skF_6','#skF_6')
      | m1_subset_1('#skF_1'(A_3501,'#skF_6',u1_struct_0('#skF_5')),B_3500)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_3500)
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3501))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3501)) ) ),
    inference(resolution,[status(thm)],[c_84958,c_56514])).

tff(c_85831,plain,(
    ! [A_3501,B_3500] :
      ( m1_subset_1('#skF_1'(A_3501,'#skF_6',u1_struct_0('#skF_5')),B_3500)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_3500)
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3501))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3501)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85278])).

tff(c_85997,plain,(
    ! [A_3505,B_3506] :
      ( m1_subset_1('#skF_1'(A_3505,'#skF_6',u1_struct_0('#skF_5')),B_3506)
      | ~ r1_tarski(u1_struct_0('#skF_5'),B_3506)
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3505))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3505)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57894,c_85831])).

tff(c_68,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_180,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1(k1_yellow_0(A_84,B_85),u1_struct_0(A_84))
      | ~ l1_orders_2(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_183,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_180])).

tff(c_185,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_183])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_78,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_76,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_44,plain,(
    ! [A_36] :
      ( r1_yellow_0(A_36,k1_xboole_0)
      | ~ l1_orders_2(A_36)
      | ~ v1_yellow_0(A_36)
      | ~ v5_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56476,plain,(
    ! [A_2222,B_2223,D_2224] :
      ( r1_orders_2(A_2222,k1_yellow_0(A_2222,B_2223),D_2224)
      | ~ r2_lattice3(A_2222,B_2223,D_2224)
      | ~ m1_subset_1(D_2224,u1_struct_0(A_2222))
      | ~ r1_yellow_0(A_2222,B_2223)
      | ~ m1_subset_1(k1_yellow_0(A_2222,B_2223),u1_struct_0(A_2222))
      | ~ l1_orders_2(A_2222) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56489,plain,(
    ! [D_2224] :
      ( r1_orders_2('#skF_5',k1_yellow_0('#skF_5',k1_xboole_0),D_2224)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_2224)
      | ~ m1_subset_1(D_2224,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_56476])).

tff(c_56502,plain,(
    ! [D_2224] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),D_2224)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_2224)
      | ~ m1_subset_1(D_2224,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_185,c_117,c_56489])).

tff(c_56503,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_56502])).

tff(c_56506,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_56503])).

tff(c_56509,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_56506])).

tff(c_56511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_56509])).

tff(c_56512,plain,(
    ! [D_2224] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),D_2224)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_2224)
      | ~ m1_subset_1(D_2224,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_56502])).

tff(c_56552,plain,(
    ! [D_2231,B_2232,A_2233,C_2234] :
      ( r2_hidden(D_2231,B_2232)
      | ~ r1_orders_2(A_2233,C_2234,D_2231)
      | ~ r2_hidden(C_2234,B_2232)
      | ~ m1_subset_1(D_2231,u1_struct_0(A_2233))
      | ~ m1_subset_1(C_2234,u1_struct_0(A_2233))
      | ~ v13_waybel_0(B_2232,A_2233)
      | ~ m1_subset_1(B_2232,k1_zfmisc_1(u1_struct_0(A_2233)))
      | ~ l1_orders_2(A_2233) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56554,plain,(
    ! [D_2224,B_2232] :
      ( r2_hidden(D_2224,B_2232)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_2232)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_2232,'#skF_5')
      | ~ m1_subset_1(B_2232,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_2224)
      | ~ m1_subset_1(D_2224,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_56512,c_56552])).

tff(c_70035,plain,(
    ! [D_3035,B_3036] :
      ( r2_hidden(D_3035,B_3036)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_3036)
      | ~ v13_waybel_0(B_3036,'#skF_5')
      | ~ m1_subset_1(B_3036,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_3035)
      | ~ m1_subset_1(D_3035,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_185,c_56554])).

tff(c_70085,plain,(
    ! [D_3035] :
      ( r2_hidden(D_3035,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_3035)
      | ~ m1_subset_1(D_3035,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_66,c_70035])).

tff(c_70104,plain,(
    ! [D_3035] :
      ( r2_hidden(D_3035,'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_3035)
      | ~ m1_subset_1(D_3035,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_177,c_70085])).

tff(c_86090,plain,(
    ! [A_3505] :
      ( r2_hidden('#skF_1'(A_3505,'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_1'(A_3505,'#skF_6',u1_struct_0('#skF_5')))
      | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3505))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_3505)) ) ),
    inference(resolution,[status(thm)],[c_85997,c_70104])).

tff(c_115323,plain,(
    ! [A_4086] :
      ( r2_hidden('#skF_1'(A_4086,'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_1'(A_4086,'#skF_6',u1_struct_0('#skF_5')))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_4086))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_4086)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_86090])).

tff(c_115341,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ l1_orders_2('#skF_5')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_55737,c_115323])).

tff(c_115358,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74,c_115341])).

tff(c_115359,plain,
    ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_57894,c_115358])).

tff(c_115362,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_115359])).

tff(c_115365,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_115362])).

tff(c_115369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_115365])).

tff(c_115371,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_115359])).

tff(c_115370,plain,(
    r2_hidden('#skF_1'(u1_struct_0('#skF_5'),'#skF_6',u1_struct_0('#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_115359])).

tff(c_60165,plain,(
    ! [A_2563,B_2564,C_2565,B_2566] :
      ( m1_subset_1('#skF_1'(A_2563,B_2564,C_2565),B_2566)
      | ~ r1_tarski(B_2564,B_2566)
      | r2_hidden('#skF_1'(A_2563,B_2564,C_2565),C_2565)
      | C_2565 = B_2564
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(A_2563))
      | ~ m1_subset_1(B_2564,k1_zfmisc_1(A_2563)) ) ),
    inference(resolution,[status(thm)],[c_55932,c_243])).

tff(c_100925,plain,(
    ! [C_3789,B_3786,A_3788,B_3790,B_3787] :
      ( r2_hidden('#skF_1'(A_3788,B_3790,C_3789),B_3787)
      | v1_xboole_0(B_3786)
      | ~ r1_tarski(B_3786,B_3787)
      | ~ r1_tarski(B_3790,B_3786)
      | r2_hidden('#skF_1'(A_3788,B_3790,C_3789),C_3789)
      | C_3789 = B_3790
      | ~ m1_subset_1(C_3789,k1_zfmisc_1(A_3788))
      | ~ m1_subset_1(B_3790,k1_zfmisc_1(A_3788)) ) ),
    inference(resolution,[status(thm)],[c_60165,c_632])).

tff(c_100955,plain,(
    ! [A_3788,B_3790,C_3789] :
      ( r2_hidden('#skF_1'(A_3788,B_3790,C_3789),u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ r1_tarski(B_3790,'#skF_6')
      | r2_hidden('#skF_1'(A_3788,B_3790,C_3789),C_3789)
      | C_3789 = B_3790
      | ~ m1_subset_1(C_3789,k1_zfmisc_1(A_3788))
      | ~ m1_subset_1(B_3790,k1_zfmisc_1(A_3788)) ) ),
    inference(resolution,[status(thm)],[c_104,c_100925])).

tff(c_100974,plain,(
    ! [A_3788,B_3790,C_3789] :
      ( r2_hidden('#skF_1'(A_3788,B_3790,C_3789),u1_struct_0('#skF_5'))
      | ~ r1_tarski(B_3790,'#skF_6')
      | r2_hidden('#skF_1'(A_3788,B_3790,C_3789),C_3789)
      | C_3789 = B_3790
      | ~ m1_subset_1(C_3789,k1_zfmisc_1(A_3788))
      | ~ m1_subset_1(B_3790,k1_zfmisc_1(A_3788)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_100955])).

tff(c_101132,plain,(
    ! [B_3794,A_3795] :
      ( ~ r1_tarski(B_3794,'#skF_6')
      | u1_struct_0('#skF_5') = B_3794
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3795))
      | ~ m1_subset_1(B_3794,k1_zfmisc_1(A_3795))
      | r2_hidden('#skF_1'(A_3795,B_3794,u1_struct_0('#skF_5')),u1_struct_0('#skF_5')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_100974])).

tff(c_12,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | ~ r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101183,plain,(
    ! [A_3795,B_3794] :
      ( ~ r2_hidden('#skF_1'(A_3795,B_3794,u1_struct_0('#skF_5')),B_3794)
      | ~ r1_tarski(B_3794,'#skF_6')
      | u1_struct_0('#skF_5') = B_3794
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_3795))
      | ~ m1_subset_1(B_3794,k1_zfmisc_1(A_3795)) ) ),
    inference(resolution,[status(thm)],[c_101132,c_12])).

tff(c_116018,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | u1_struct_0('#skF_5') = '#skF_6'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_115370,c_101183])).

tff(c_116064,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_115371,c_6,c_116018])).

tff(c_116066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57894,c_116064])).

tff(c_116067,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56289])).

tff(c_116073,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116067,c_56164])).

tff(c_116103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_116073])).

tff(c_116104,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56163])).

tff(c_186,plain,(
    ! [B_86,A_87] :
      ( B_86 = A_87
      | ~ r1_tarski(B_86,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_186])).

tff(c_196,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_116128,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116104,c_196])).

tff(c_116137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116128])).

tff(c_116138,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56058])).

tff(c_116201,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116138,c_196])).

tff(c_116210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116201])).

tff(c_116211,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_176,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_116214,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116211,c_176])).

tff(c_116218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_116214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.05/43.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.05/43.23  
% 53.05/43.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.05/43.23  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 53.05/43.23  
% 53.05/43.23  %Foreground sorts:
% 53.05/43.23  
% 53.05/43.23  
% 53.05/43.23  %Background operators:
% 53.05/43.23  
% 53.05/43.23  
% 53.05/43.23  %Foreground operators:
% 53.05/43.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 53.05/43.23  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 53.05/43.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 53.05/43.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 53.05/43.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.05/43.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 53.05/43.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 53.05/43.23  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 53.05/43.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 53.05/43.23  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 53.05/43.23  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 53.05/43.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 53.05/43.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 53.05/43.23  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 53.05/43.23  tff('#skF_5', type, '#skF_5': $i).
% 53.05/43.23  tff('#skF_6', type, '#skF_6': $i).
% 53.05/43.23  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 53.05/43.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 53.05/43.23  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 53.05/43.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 53.05/43.23  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 53.05/43.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 53.05/43.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 53.05/43.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 53.05/43.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.05/43.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.05/43.23  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 53.05/43.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 53.05/43.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 53.05/43.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 53.05/43.23  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 53.05/43.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 53.05/43.23  
% 53.05/43.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 53.05/43.26  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 53.05/43.26  tff(f_142, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 53.05/43.26  tff(f_171, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 53.05/43.26  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 53.05/43.26  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 53.05/43.26  tff(f_94, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 53.05/43.26  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 53.05/43.26  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 53.05/43.26  tff(f_68, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 53.05/43.26  tff(f_116, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 53.05/43.26  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 53.05/43.26  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 53.05/43.26  tff(f_135, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 53.05/43.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.05/43.26  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 53.05/43.26  tff(c_105, plain, (![B_73]: (~v1_subset_1(B_73, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 53.05/43.26  tff(c_109, plain, (![B_17]: (~v1_subset_1(B_17, B_17) | ~r1_tarski(B_17, B_17))), inference(resolution, [status(thm)], [c_24, c_105])).
% 53.05/43.26  tff(c_112, plain, (![B_17]: (~v1_subset_1(B_17, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 53.05/43.26  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_72, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_20, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 53.05/43.26  tff(c_92, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_124, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_92])).
% 53.05/43.26  tff(c_127, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_124])).
% 53.05/43.26  tff(c_130, plain, (~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_127])).
% 53.05/43.26  tff(c_86, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_131, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_124, c_86])).
% 53.05/43.26  tff(c_149, plain, (![B_82, A_83]: (v1_subset_1(B_82, A_83) | B_82=A_83 | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 53.05/43.26  tff(c_155, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_66, c_149])).
% 53.05/43.26  tff(c_159, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_131, c_155])).
% 53.05/43.26  tff(c_96, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 53.05/43.26  tff(c_104, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_96])).
% 53.05/43.26  tff(c_138, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.05/43.26  tff(c_143, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_104, c_138])).
% 53.05/43.26  tff(c_148, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_143])).
% 53.05/43.26  tff(c_160, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_148])).
% 53.05/43.26  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_160])).
% 53.05/43.26  tff(c_168, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_143])).
% 53.05/43.26  tff(c_74, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_113, plain, (![A_74]: (k1_yellow_0(A_74, k1_xboole_0)=k3_yellow_0(A_74) | ~l1_orders_2(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 53.05/43.26  tff(c_117, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_113])).
% 53.05/43.26  tff(c_132, plain, (![A_78, B_79]: (m1_subset_1(k1_yellow_0(A_78, B_79), u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_94])).
% 53.05/43.26  tff(c_135, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_117, c_132])).
% 53.05/43.26  tff(c_137, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_135])).
% 53.05/43.26  tff(c_170, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_137])).
% 53.05/43.26  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_170])).
% 53.05/43.26  tff(c_177, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_92])).
% 53.05/43.26  tff(c_216, plain, (![C_92, A_93, B_94]: (r2_hidden(C_92, A_93) | ~r2_hidden(C_92, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 53.05/43.26  tff(c_223, plain, (![A_95]: (r2_hidden(k3_yellow_0('#skF_5'), A_95) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_177, c_216])).
% 53.05/43.26  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 53.05/43.26  tff(c_259, plain, (![A_105, A_106]: (r2_hidden(k3_yellow_0('#skF_5'), A_105) | ~m1_subset_1(A_106, k1_zfmisc_1(A_105)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_106)))), inference(resolution, [status(thm)], [c_223, c_8])).
% 53.05/43.26  tff(c_265, plain, (r2_hidden(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_259])).
% 53.05/43.26  tff(c_304, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_265])).
% 53.05/43.26  tff(c_307, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_304])).
% 53.05/43.26  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 53.05/43.26  tff(c_313, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_265])).
% 53.05/43.26  tff(c_55692, plain, (![A_2116, B_2117, C_2118]: (m1_subset_1('#skF_1'(A_2116, B_2117, C_2118), A_2116) | C_2118=B_2117 | ~m1_subset_1(C_2118, k1_zfmisc_1(A_2116)) | ~m1_subset_1(B_2117, k1_zfmisc_1(A_2116)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.05/43.26  tff(c_614, plain, (![A_152, A_153, B_154]: (r2_hidden(A_152, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)) | v1_xboole_0(B_154) | ~m1_subset_1(A_152, B_154))), inference(resolution, [status(thm)], [c_20, c_216])).
% 53.05/43.26  tff(c_632, plain, (![A_152, B_17, A_16]: (r2_hidden(A_152, B_17) | v1_xboole_0(A_16) | ~m1_subset_1(A_152, A_16) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_24, c_614])).
% 53.05/43.26  tff(c_57408, plain, (![A_2350, B_2351, C_2352, B_2353]: (r2_hidden('#skF_1'(A_2350, B_2351, C_2352), B_2353) | v1_xboole_0(A_2350) | ~r1_tarski(A_2350, B_2353) | C_2352=B_2351 | ~m1_subset_1(C_2352, k1_zfmisc_1(A_2350)) | ~m1_subset_1(B_2351, k1_zfmisc_1(A_2350)))), inference(resolution, [status(thm)], [c_55692, c_632])).
% 53.05/43.26  tff(c_26, plain, (![A_18, C_20, B_19]: (m1_subset_1(A_18, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 53.05/43.26  tff(c_349, plain, (![A_18]: (m1_subset_1(A_18, '#skF_6') | ~r2_hidden(A_18, '#skF_6'))), inference(resolution, [status(thm)], [c_313, c_26])).
% 53.05/43.26  tff(c_57808, plain, (![A_2394, B_2395, C_2396]: (m1_subset_1('#skF_1'(A_2394, B_2395, C_2396), '#skF_6') | v1_xboole_0(A_2394) | ~r1_tarski(A_2394, '#skF_6') | C_2396=B_2395 | ~m1_subset_1(C_2396, k1_zfmisc_1(A_2394)) | ~m1_subset_1(B_2395, k1_zfmisc_1(A_2394)))), inference(resolution, [status(thm)], [c_57408, c_349])).
% 53.05/43.26  tff(c_619, plain, (![A_152]: (r2_hidden(A_152, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_152, '#skF_6'))), inference(resolution, [status(thm)], [c_313, c_614])).
% 53.05/43.26  tff(c_630, plain, (![A_152]: (r2_hidden(A_152, '#skF_6') | ~m1_subset_1(A_152, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_619])).
% 53.05/43.26  tff(c_626, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_152, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_614])).
% 53.05/43.26  tff(c_635, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_5')) | ~m1_subset_1(A_152, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_626])).
% 53.05/43.26  tff(c_55992, plain, (![A_2161, B_2162, C_2163]: (~r2_hidden('#skF_1'(A_2161, B_2162, C_2163), C_2163) | ~r2_hidden('#skF_1'(A_2161, B_2162, C_2163), B_2162) | C_2163=B_2162 | ~m1_subset_1(C_2163, k1_zfmisc_1(A_2161)) | ~m1_subset_1(B_2162, k1_zfmisc_1(A_2161)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.05/43.26  tff(c_56251, plain, (![A_2198, B_2199]: (~r2_hidden('#skF_1'(A_2198, B_2199, u1_struct_0('#skF_5')), B_2199) | u1_struct_0('#skF_5')=B_2199 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2198)) | ~m1_subset_1(B_2199, k1_zfmisc_1(A_2198)) | ~m1_subset_1('#skF_1'(A_2198, B_2199, u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_635, c_55992])).
% 53.05/43.26  tff(c_56289, plain, (![A_2198]: (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2198)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2198)) | ~m1_subset_1('#skF_1'(A_2198, '#skF_6', u1_struct_0('#skF_5')), '#skF_6'))), inference(resolution, [status(thm)], [c_630, c_56251])).
% 53.05/43.26  tff(c_56514, plain, (![A_2198]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2198)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2198)) | ~m1_subset_1('#skF_1'(A_2198, '#skF_6', u1_struct_0('#skF_5')), '#skF_6'))), inference(splitLeft, [status(thm)], [c_56289])).
% 53.05/43.26  tff(c_57839, plain, (![A_2394]: (v1_xboole_0(A_2394) | ~r1_tarski(A_2394, '#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2394)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2394)))), inference(resolution, [status(thm)], [c_57808, c_56514])).
% 53.05/43.26  tff(c_57844, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_57839])).
% 53.05/43.26  tff(c_10, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.05/43.26  tff(c_56023, plain, (![A_2164, B_2165]: (~r2_hidden('#skF_1'(A_2164, B_2165, '#skF_6'), B_2165) | B_2165='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2164)) | ~m1_subset_1(B_2165, k1_zfmisc_1(A_2164)) | ~m1_subset_1('#skF_1'(A_2164, B_2165, '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_630, c_55992])).
% 53.05/43.26  tff(c_56058, plain, (![A_2164]: (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2164)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2164)) | ~m1_subset_1('#skF_1'(A_2164, u1_struct_0('#skF_5'), '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_635, c_56023])).
% 53.05/43.26  tff(c_56156, plain, (![A_2185]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_2185)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_2185)) | ~m1_subset_1('#skF_1'(A_2185, u1_struct_0('#skF_5'), '#skF_6'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_56058])).
% 53.05/43.26  tff(c_56160, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_56156])).
% 53.05/43.26  tff(c_56163, plain, (u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_56160])).
% 53.05/43.26  tff(c_56164, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_56163])).
% 53.05/43.26  tff(c_57862, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_57844, c_56164])).
% 53.05/43.26  tff(c_57892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_57862])).
% 53.05/43.26  tff(c_57894, plain, (u1_struct_0('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_57839])).
% 53.05/43.26  tff(c_48, plain, (![A_37, B_39]: (r2_lattice3(A_37, k1_xboole_0, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 53.05/43.26  tff(c_55737, plain, (![A_37, B_2117, C_2118]: (r2_lattice3(A_37, k1_xboole_0, '#skF_1'(u1_struct_0(A_37), B_2117, C_2118)) | ~l1_orders_2(A_37) | C_2118=B_2117 | ~m1_subset_1(C_2118, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_2117, k1_zfmisc_1(u1_struct_0(A_37))))), inference(resolution, [status(thm)], [c_55692, c_48])).
% 53.05/43.26  tff(c_55932, plain, (![A_2151, B_2152, C_2153]: (r2_hidden('#skF_1'(A_2151, B_2152, C_2153), B_2152) | r2_hidden('#skF_1'(A_2151, B_2152, C_2153), C_2153) | C_2153=B_2152 | ~m1_subset_1(C_2153, k1_zfmisc_1(A_2151)) | ~m1_subset_1(B_2152, k1_zfmisc_1(A_2151)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.05/43.26  tff(c_238, plain, (![A_98, C_99, B_100]: (m1_subset_1(A_98, C_99) | ~m1_subset_1(B_100, k1_zfmisc_1(C_99)) | ~r2_hidden(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_68])).
% 53.05/43.26  tff(c_243, plain, (![A_98, B_17, A_16]: (m1_subset_1(A_98, B_17) | ~r2_hidden(A_98, A_16) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_24, c_238])).
% 53.05/43.26  tff(c_60803, plain, (![A_2584, B_2585, C_2586, B_2587]: (m1_subset_1('#skF_1'(A_2584, B_2585, C_2586), B_2587) | ~r1_tarski(C_2586, B_2587) | r2_hidden('#skF_1'(A_2584, B_2585, C_2586), B_2585) | C_2586=B_2585 | ~m1_subset_1(C_2586, k1_zfmisc_1(A_2584)) | ~m1_subset_1(B_2585, k1_zfmisc_1(A_2584)))), inference(resolution, [status(thm)], [c_55932, c_243])).
% 53.05/43.26  tff(c_84958, plain, (![B_3500, B_3503, C_3502, A_3501, B_3504]: (m1_subset_1('#skF_1'(A_3501, B_3504, C_3502), B_3503) | ~r1_tarski(B_3504, B_3503) | m1_subset_1('#skF_1'(A_3501, B_3504, C_3502), B_3500) | ~r1_tarski(C_3502, B_3500) | C_3502=B_3504 | ~m1_subset_1(C_3502, k1_zfmisc_1(A_3501)) | ~m1_subset_1(B_3504, k1_zfmisc_1(A_3501)))), inference(resolution, [status(thm)], [c_60803, c_243])).
% 53.05/43.26  tff(c_85278, plain, (![A_3501, B_3500]: (~r1_tarski('#skF_6', '#skF_6') | m1_subset_1('#skF_1'(A_3501, '#skF_6', u1_struct_0('#skF_5')), B_3500) | ~r1_tarski(u1_struct_0('#skF_5'), B_3500) | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3501)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3501)))), inference(resolution, [status(thm)], [c_84958, c_56514])).
% 53.05/43.26  tff(c_85831, plain, (![A_3501, B_3500]: (m1_subset_1('#skF_1'(A_3501, '#skF_6', u1_struct_0('#skF_5')), B_3500) | ~r1_tarski(u1_struct_0('#skF_5'), B_3500) | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3501)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3501)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85278])).
% 53.05/43.26  tff(c_85997, plain, (![A_3505, B_3506]: (m1_subset_1('#skF_1'(A_3505, '#skF_6', u1_struct_0('#skF_5')), B_3506) | ~r1_tarski(u1_struct_0('#skF_5'), B_3506) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3505)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3505)))), inference(negUnitSimplification, [status(thm)], [c_57894, c_85831])).
% 53.05/43.26  tff(c_68, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_180, plain, (![A_84, B_85]: (m1_subset_1(k1_yellow_0(A_84, B_85), u1_struct_0(A_84)) | ~l1_orders_2(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 53.05/43.26  tff(c_183, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_117, c_180])).
% 53.05/43.26  tff(c_185, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_183])).
% 53.05/43.26  tff(c_84, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_78, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_76, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 53.05/43.26  tff(c_44, plain, (![A_36]: (r1_yellow_0(A_36, k1_xboole_0) | ~l1_orders_2(A_36) | ~v1_yellow_0(A_36) | ~v5_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 53.05/43.26  tff(c_56476, plain, (![A_2222, B_2223, D_2224]: (r1_orders_2(A_2222, k1_yellow_0(A_2222, B_2223), D_2224) | ~r2_lattice3(A_2222, B_2223, D_2224) | ~m1_subset_1(D_2224, u1_struct_0(A_2222)) | ~r1_yellow_0(A_2222, B_2223) | ~m1_subset_1(k1_yellow_0(A_2222, B_2223), u1_struct_0(A_2222)) | ~l1_orders_2(A_2222))), inference(cnfTransformation, [status(thm)], [f_90])).
% 53.05/43.26  tff(c_56489, plain, (![D_2224]: (r1_orders_2('#skF_5', k1_yellow_0('#skF_5', k1_xboole_0), D_2224) | ~r2_lattice3('#skF_5', k1_xboole_0, D_2224) | ~m1_subset_1(D_2224, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_56476])).
% 53.05/43.26  tff(c_56502, plain, (![D_2224]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), D_2224) | ~r2_lattice3('#skF_5', k1_xboole_0, D_2224) | ~m1_subset_1(D_2224, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_185, c_117, c_56489])).
% 53.05/43.26  tff(c_56503, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_56502])).
% 53.05/43.26  tff(c_56506, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_56503])).
% 53.05/43.26  tff(c_56509, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_56506])).
% 53.05/43.26  tff(c_56511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_56509])).
% 53.05/43.26  tff(c_56512, plain, (![D_2224]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), D_2224) | ~r2_lattice3('#skF_5', k1_xboole_0, D_2224) | ~m1_subset_1(D_2224, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_56502])).
% 53.05/43.26  tff(c_56552, plain, (![D_2231, B_2232, A_2233, C_2234]: (r2_hidden(D_2231, B_2232) | ~r1_orders_2(A_2233, C_2234, D_2231) | ~r2_hidden(C_2234, B_2232) | ~m1_subset_1(D_2231, u1_struct_0(A_2233)) | ~m1_subset_1(C_2234, u1_struct_0(A_2233)) | ~v13_waybel_0(B_2232, A_2233) | ~m1_subset_1(B_2232, k1_zfmisc_1(u1_struct_0(A_2233))) | ~l1_orders_2(A_2233))), inference(cnfTransformation, [status(thm)], [f_135])).
% 53.05/43.26  tff(c_56554, plain, (![D_2224, B_2232]: (r2_hidden(D_2224, B_2232) | ~r2_hidden(k3_yellow_0('#skF_5'), B_2232) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_2232, '#skF_5') | ~m1_subset_1(B_2232, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~r2_lattice3('#skF_5', k1_xboole_0, D_2224) | ~m1_subset_1(D_2224, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_56512, c_56552])).
% 53.05/43.26  tff(c_70035, plain, (![D_3035, B_3036]: (r2_hidden(D_3035, B_3036) | ~r2_hidden(k3_yellow_0('#skF_5'), B_3036) | ~v13_waybel_0(B_3036, '#skF_5') | ~m1_subset_1(B_3036, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_lattice3('#skF_5', k1_xboole_0, D_3035) | ~m1_subset_1(D_3035, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_185, c_56554])).
% 53.05/43.26  tff(c_70085, plain, (![D_3035]: (r2_hidden(D_3035, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~r2_lattice3('#skF_5', k1_xboole_0, D_3035) | ~m1_subset_1(D_3035, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_66, c_70035])).
% 53.05/43.26  tff(c_70104, plain, (![D_3035]: (r2_hidden(D_3035, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, D_3035) | ~m1_subset_1(D_3035, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_177, c_70085])).
% 53.05/43.26  tff(c_86090, plain, (![A_3505]: (r2_hidden('#skF_1'(A_3505, '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_1'(A_3505, '#skF_6', u1_struct_0('#skF_5'))) | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3505)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_3505)))), inference(resolution, [status(thm)], [c_85997, c_70104])).
% 53.05/43.26  tff(c_115323, plain, (![A_4086]: (r2_hidden('#skF_1'(A_4086, '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_1'(A_4086, '#skF_6', u1_struct_0('#skF_5'))) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_4086)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_4086)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_86090])).
% 53.05/43.26  tff(c_115341, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~l1_orders_2('#skF_5') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_55737, c_115323])).
% 53.05/43.26  tff(c_115358, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74, c_115341])).
% 53.05/43.26  tff(c_115359, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_57894, c_115358])).
% 53.05/43.26  tff(c_115362, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_115359])).
% 53.05/43.26  tff(c_115365, plain, (~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_115362])).
% 53.05/43.26  tff(c_115369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_115365])).
% 53.05/43.26  tff(c_115371, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_115359])).
% 53.05/43.26  tff(c_115370, plain, (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), '#skF_6', u1_struct_0('#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_115359])).
% 53.05/43.26  tff(c_60165, plain, (![A_2563, B_2564, C_2565, B_2566]: (m1_subset_1('#skF_1'(A_2563, B_2564, C_2565), B_2566) | ~r1_tarski(B_2564, B_2566) | r2_hidden('#skF_1'(A_2563, B_2564, C_2565), C_2565) | C_2565=B_2564 | ~m1_subset_1(C_2565, k1_zfmisc_1(A_2563)) | ~m1_subset_1(B_2564, k1_zfmisc_1(A_2563)))), inference(resolution, [status(thm)], [c_55932, c_243])).
% 53.05/43.26  tff(c_100925, plain, (![C_3789, B_3786, A_3788, B_3790, B_3787]: (r2_hidden('#skF_1'(A_3788, B_3790, C_3789), B_3787) | v1_xboole_0(B_3786) | ~r1_tarski(B_3786, B_3787) | ~r1_tarski(B_3790, B_3786) | r2_hidden('#skF_1'(A_3788, B_3790, C_3789), C_3789) | C_3789=B_3790 | ~m1_subset_1(C_3789, k1_zfmisc_1(A_3788)) | ~m1_subset_1(B_3790, k1_zfmisc_1(A_3788)))), inference(resolution, [status(thm)], [c_60165, c_632])).
% 53.05/43.26  tff(c_100955, plain, (![A_3788, B_3790, C_3789]: (r2_hidden('#skF_1'(A_3788, B_3790, C_3789), u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~r1_tarski(B_3790, '#skF_6') | r2_hidden('#skF_1'(A_3788, B_3790, C_3789), C_3789) | C_3789=B_3790 | ~m1_subset_1(C_3789, k1_zfmisc_1(A_3788)) | ~m1_subset_1(B_3790, k1_zfmisc_1(A_3788)))), inference(resolution, [status(thm)], [c_104, c_100925])).
% 53.05/43.26  tff(c_100974, plain, (![A_3788, B_3790, C_3789]: (r2_hidden('#skF_1'(A_3788, B_3790, C_3789), u1_struct_0('#skF_5')) | ~r1_tarski(B_3790, '#skF_6') | r2_hidden('#skF_1'(A_3788, B_3790, C_3789), C_3789) | C_3789=B_3790 | ~m1_subset_1(C_3789, k1_zfmisc_1(A_3788)) | ~m1_subset_1(B_3790, k1_zfmisc_1(A_3788)))), inference(negUnitSimplification, [status(thm)], [c_72, c_100955])).
% 53.05/43.26  tff(c_101132, plain, (![B_3794, A_3795]: (~r1_tarski(B_3794, '#skF_6') | u1_struct_0('#skF_5')=B_3794 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3795)) | ~m1_subset_1(B_3794, k1_zfmisc_1(A_3795)) | r2_hidden('#skF_1'(A_3795, B_3794, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')))), inference(factorization, [status(thm), theory('equality')], [c_100974])).
% 53.05/43.26  tff(c_12, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | ~r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.05/43.26  tff(c_101183, plain, (![A_3795, B_3794]: (~r2_hidden('#skF_1'(A_3795, B_3794, u1_struct_0('#skF_5')), B_3794) | ~r1_tarski(B_3794, '#skF_6') | u1_struct_0('#skF_5')=B_3794 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_3795)) | ~m1_subset_1(B_3794, k1_zfmisc_1(A_3795)))), inference(resolution, [status(thm)], [c_101132, c_12])).
% 53.05/43.26  tff(c_116018, plain, (~r1_tarski('#skF_6', '#skF_6') | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_115370, c_101183])).
% 53.05/43.26  tff(c_116064, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_115371, c_6, c_116018])).
% 53.05/43.26  tff(c_116066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57894, c_116064])).
% 53.05/43.26  tff(c_116067, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_56289])).
% 53.05/43.26  tff(c_116073, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_116067, c_56164])).
% 53.05/43.26  tff(c_116103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_116073])).
% 53.05/43.26  tff(c_116104, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_56163])).
% 53.05/43.26  tff(c_186, plain, (![B_86, A_87]: (B_86=A_87 | ~r1_tarski(B_86, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.05/43.26  tff(c_191, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_104, c_186])).
% 53.05/43.26  tff(c_196, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_191])).
% 53.05/43.26  tff(c_116128, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116104, c_196])).
% 53.05/43.26  tff(c_116137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_116128])).
% 53.05/43.26  tff(c_116138, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_56058])).
% 53.05/43.26  tff(c_116201, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116138, c_196])).
% 53.05/43.26  tff(c_116210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_116201])).
% 53.05/43.26  tff(c_116211, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_191])).
% 53.05/43.26  tff(c_176, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_92])).
% 53.05/43.26  tff(c_116214, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116211, c_176])).
% 53.05/43.26  tff(c_116218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_116214])).
% 53.05/43.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.05/43.26  
% 53.05/43.26  Inference rules
% 53.05/43.26  ----------------------
% 53.05/43.26  #Ref     : 0
% 53.05/43.26  #Sup     : 25245
% 53.05/43.26  #Fact    : 52
% 53.05/43.26  #Define  : 0
% 53.05/43.26  #Split   : 54
% 53.05/43.26  #Chain   : 0
% 53.05/43.26  #Close   : 0
% 53.05/43.26  
% 53.05/43.26  Ordering : KBO
% 53.05/43.26  
% 53.05/43.26  Simplification rules
% 53.05/43.26  ----------------------
% 53.05/43.26  #Subsume      : 7447
% 53.05/43.26  #Demod        : 5761
% 53.05/43.26  #Tautology    : 1112
% 53.05/43.26  #SimpNegUnit  : 1967
% 53.05/43.26  #BackRed      : 414
% 53.05/43.26  
% 53.05/43.26  #Partial instantiations: 0
% 53.05/43.26  #Strategies tried      : 1
% 53.05/43.26  
% 53.05/43.26  Timing (in seconds)
% 53.05/43.26  ----------------------
% 53.05/43.26  Preprocessing        : 0.33
% 53.05/43.26  Parsing              : 0.17
% 53.05/43.26  CNF conversion       : 0.03
% 53.05/43.26  Main loop            : 42.10
% 53.05/43.26  Inferencing          : 4.78
% 53.05/43.26  Reduction            : 6.66
% 53.05/43.26  Demodulation         : 4.68
% 53.05/43.26  BG Simplification    : 0.41
% 53.05/43.26  Subsumption          : 28.55
% 53.05/43.26  Abstraction          : 0.70
% 53.05/43.26  MUC search           : 0.00
% 53.05/43.26  Cooper               : 0.00
% 53.05/43.26  Total                : 42.48
% 53.05/43.26  Index Insertion      : 0.00
% 53.05/43.26  Index Deletion       : 0.00
% 53.05/43.26  Index Matching       : 0.00
% 53.05/43.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
