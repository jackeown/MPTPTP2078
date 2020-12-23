%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 326 expanded)
%              Number of leaves         :   44 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          :  210 (1207 expanded)
%              Number of equality atoms :   17 (  88 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_132,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_125,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_66,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),A_5)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_212,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden('#skF_3'(A_104,B_105,C_106),B_105)
      | r2_lattice3(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [B_107,A_108,C_109] :
      ( ~ v1_xboole_0(B_107)
      | r2_lattice3(A_108,B_107,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_230,plain,(
    ! [B_107,A_108,B_6] :
      ( ~ v1_xboole_0(B_107)
      | r2_lattice3(A_108,B_107,'#skF_2'(u1_struct_0(A_108),B_6))
      | ~ l1_orders_2(A_108)
      | u1_struct_0(A_108) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_108))) ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_60,plain,(
    v13_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_109,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,B_77)
      | v1_xboole_0(B_77)
      | ~ m1_subset_1(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,
    ( r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
    | ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_97,plain,(
    ~ v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_108,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_84])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_109,c_108])).

tff(c_118,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_112])).

tff(c_120,plain,(
    ! [B_78,A_79] :
      ( v1_subset_1(B_78,A_79)
      | B_78 = A_79
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_123,plain,
    ( v1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | u1_struct_0('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_58,c_120])).

tff(c_126,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_123])).

tff(c_92,plain,(
    ! [A_73] :
      ( k1_yellow_0(A_73,k1_xboole_0) = k3_yellow_0(A_73)
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    k1_yellow_0('#skF_7',k1_xboole_0) = k3_yellow_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_102,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_yellow_0(A_74,B_75),u1_struct_0(A_74))
      | ~ l1_orders_2(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_105,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_102])).

tff(c_107,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_105])).

tff(c_127,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_107])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_127])).

tff(c_132,plain,(
    r2_hidden(k3_yellow_0('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_149,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k1_yellow_0(A_82,B_83),u1_struct_0(A_82))
      | ~ l1_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_152,plain,
    ( m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_149])).

tff(c_154,plain,(
    m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_152])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_70,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    v1_yellow_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    ! [A_40] :
      ( r1_yellow_0(A_40,k1_xboole_0)
      | ~ l1_orders_2(A_40)
      | ~ v1_yellow_0(A_40)
      | ~ v5_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_952,plain,(
    ! [A_228,B_229] :
      ( r2_lattice3(A_228,B_229,k1_yellow_0(A_228,B_229))
      | ~ r1_yellow_0(A_228,B_229)
      | ~ m1_subset_1(k1_yellow_0(A_228,B_229),u1_struct_0(A_228))
      | ~ l1_orders_2(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_959,plain,
    ( r2_lattice3('#skF_7',k1_xboole_0,k1_yellow_0('#skF_7',k1_xboole_0))
    | ~ r1_yellow_0('#skF_7',k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_orders_2('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_952])).

tff(c_965,plain,
    ( r2_lattice3('#skF_7',k1_xboole_0,k3_yellow_0('#skF_7'))
    | ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_96,c_959])).

tff(c_966,plain,(
    ~ r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_969,plain,
    ( ~ l1_orders_2('#skF_7')
    | ~ v1_yellow_0('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_966])).

tff(c_972,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_969])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_972])).

tff(c_976,plain,(
    r1_yellow_0('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_1354,plain,(
    ! [A_307,B_308,D_309] :
      ( r1_orders_2(A_307,k1_yellow_0(A_307,B_308),D_309)
      | ~ r2_lattice3(A_307,B_308,D_309)
      | ~ m1_subset_1(D_309,u1_struct_0(A_307))
      | ~ r1_yellow_0(A_307,B_308)
      | ~ m1_subset_1(k1_yellow_0(A_307,B_308),u1_struct_0(A_307))
      | ~ l1_orders_2(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1361,plain,(
    ! [D_309] :
      ( r1_orders_2('#skF_7',k1_yellow_0('#skF_7',k1_xboole_0),D_309)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_309)
      | ~ m1_subset_1(D_309,u1_struct_0('#skF_7'))
      | ~ r1_yellow_0('#skF_7',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ l1_orders_2('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1354])).

tff(c_1367,plain,(
    ! [D_309] :
      ( r1_orders_2('#skF_7',k3_yellow_0('#skF_7'),D_309)
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_309)
      | ~ m1_subset_1(D_309,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_976,c_96,c_1361])).

tff(c_1443,plain,(
    ! [D_326,B_327,A_328,C_329] :
      ( r2_hidden(D_326,B_327)
      | ~ r1_orders_2(A_328,C_329,D_326)
      | ~ r2_hidden(C_329,B_327)
      | ~ m1_subset_1(D_326,u1_struct_0(A_328))
      | ~ m1_subset_1(C_329,u1_struct_0(A_328))
      | ~ v13_waybel_0(B_327,A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_orders_2(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1451,plain,(
    ! [D_309,B_327] :
      ( r2_hidden(D_309,B_327)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_327)
      | ~ m1_subset_1(k3_yellow_0('#skF_7'),u1_struct_0('#skF_7'))
      | ~ v13_waybel_0(B_327,'#skF_7')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_309)
      | ~ m1_subset_1(D_309,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1367,c_1443])).

tff(c_1483,plain,(
    ! [D_330,B_331] :
      ( r2_hidden(D_330,B_331)
      | ~ r2_hidden(k3_yellow_0('#skF_7'),B_331)
      | ~ v13_waybel_0(B_331,'#skF_7')
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_330)
      | ~ m1_subset_1(D_330,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_1451])).

tff(c_1491,plain,(
    ! [D_330] :
      ( r2_hidden(D_330,'#skF_8')
      | ~ r2_hidden(k3_yellow_0('#skF_7'),'#skF_8')
      | ~ v13_waybel_0('#skF_8','#skF_7')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_330)
      | ~ m1_subset_1(D_330,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_58,c_1483])).

tff(c_1509,plain,(
    ! [D_334] :
      ( r2_hidden(D_334,'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,D_334)
      | ~ m1_subset_1(D_334,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_132,c_1491])).

tff(c_1614,plain,(
    ! [B_337] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_337),'#skF_8')
      | ~ r2_lattice3('#skF_7',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_7'),B_337))
      | u1_struct_0('#skF_7') = B_337
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1509])).

tff(c_1618,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_6),'#skF_8')
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_orders_2('#skF_7')
      | u1_struct_0('#skF_7') = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_230,c_1614])).

tff(c_1645,plain,(
    ! [B_339] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_7'),B_339),'#skF_8')
      | u1_struct_0('#skF_7') = B_339
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6,c_1618])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | B_6 = A_5
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1655,plain,
    ( u1_struct_0('#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1645,c_8])).

tff(c_1664,plain,(
    u1_struct_0('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1655])).

tff(c_133,plain,(
    v1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1681,plain,(
    v1_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_133])).

tff(c_1682,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_58])).

tff(c_56,plain,(
    ! [B_67] :
      ( ~ v1_subset_1(B_67,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1780,plain,(
    ~ v1_subset_1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_1682,c_56])).

tff(c_1788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1780])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:50:47 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.88  
% 4.80/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.88  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 4.80/1.88  
% 4.80/1.88  %Foreground sorts:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Background operators:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Foreground operators:
% 4.80/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.80/1.88  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 4.80/1.88  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.80/1.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.88  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.80/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.80/1.88  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.80/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.88  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.80/1.88  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.80/1.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.80/1.88  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.80/1.88  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 4.80/1.88  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.80/1.88  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 4.80/1.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.80/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.80/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.88  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.80/1.88  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.80/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.80/1.88  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 4.80/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.88  
% 4.80/1.91  tff(f_161, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 4.80/1.91  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.91  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 4.80/1.91  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 4.80/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.80/1.91  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.80/1.91  tff(f_132, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.80/1.91  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 4.80/1.91  tff(f_93, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 4.80/1.91  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 4.80/1.91  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 4.80/1.91  tff(f_125, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 4.80/1.91  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_66, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.91  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1('#skF_2'(A_5, B_6), A_5) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/1.91  tff(c_212, plain, (![A_104, B_105, C_106]: (r2_hidden('#skF_3'(A_104, B_105, C_106), B_105) | r2_lattice3(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.80/1.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/1.91  tff(c_217, plain, (![B_107, A_108, C_109]: (~v1_xboole_0(B_107) | r2_lattice3(A_108, B_107, C_109) | ~m1_subset_1(C_109, u1_struct_0(A_108)) | ~l1_orders_2(A_108))), inference(resolution, [status(thm)], [c_212, c_2])).
% 4.80/1.91  tff(c_230, plain, (![B_107, A_108, B_6]: (~v1_xboole_0(B_107) | r2_lattice3(A_108, B_107, '#skF_2'(u1_struct_0(A_108), B_6)) | ~l1_orders_2(A_108) | u1_struct_0(A_108)=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_108))))), inference(resolution, [status(thm)], [c_10, c_217])).
% 4.80/1.91  tff(c_60, plain, (v13_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_64, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_109, plain, (![A_76, B_77]: (r2_hidden(A_76, B_77) | v1_xboole_0(B_77) | ~m1_subset_1(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.91  tff(c_78, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_97, plain, (~v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_78])).
% 4.80/1.91  tff(c_84, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_108, plain, (~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_97, c_84])).
% 4.80/1.91  tff(c_112, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_109, c_108])).
% 4.80/1.91  tff(c_118, plain, (~m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_112])).
% 4.80/1.91  tff(c_120, plain, (![B_78, A_79]: (v1_subset_1(B_78, A_79) | B_78=A_79 | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.80/1.91  tff(c_123, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7')) | u1_struct_0('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_58, c_120])).
% 4.80/1.91  tff(c_126, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_97, c_123])).
% 4.80/1.91  tff(c_92, plain, (![A_73]: (k1_yellow_0(A_73, k1_xboole_0)=k3_yellow_0(A_73) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.80/1.91  tff(c_96, plain, (k1_yellow_0('#skF_7', k1_xboole_0)=k3_yellow_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_92])).
% 4.80/1.91  tff(c_102, plain, (![A_74, B_75]: (m1_subset_1(k1_yellow_0(A_74, B_75), u1_struct_0(A_74)) | ~l1_orders_2(A_74))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.80/1.91  tff(c_105, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_96, c_102])).
% 4.80/1.91  tff(c_107, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_105])).
% 4.80/1.91  tff(c_127, plain, (m1_subset_1(k3_yellow_0('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_107])).
% 4.80/1.91  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_127])).
% 4.80/1.91  tff(c_132, plain, (r2_hidden(k3_yellow_0('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 4.80/1.91  tff(c_149, plain, (![A_82, B_83]: (m1_subset_1(k1_yellow_0(A_82, B_83), u1_struct_0(A_82)) | ~l1_orders_2(A_82))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.80/1.91  tff(c_152, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_96, c_149])).
% 4.80/1.91  tff(c_154, plain, (m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_152])).
% 4.80/1.91  tff(c_76, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_70, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_68, plain, (v1_yellow_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.80/1.91  tff(c_40, plain, (![A_40]: (r1_yellow_0(A_40, k1_xboole_0) | ~l1_orders_2(A_40) | ~v1_yellow_0(A_40) | ~v5_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.80/1.91  tff(c_952, plain, (![A_228, B_229]: (r2_lattice3(A_228, B_229, k1_yellow_0(A_228, B_229)) | ~r1_yellow_0(A_228, B_229) | ~m1_subset_1(k1_yellow_0(A_228, B_229), u1_struct_0(A_228)) | ~l1_orders_2(A_228))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.91  tff(c_959, plain, (r2_lattice3('#skF_7', k1_xboole_0, k1_yellow_0('#skF_7', k1_xboole_0)) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_96, c_952])).
% 4.80/1.91  tff(c_965, plain, (r2_lattice3('#skF_7', k1_xboole_0, k3_yellow_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_154, c_96, c_959])).
% 4.80/1.91  tff(c_966, plain, (~r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_965])).
% 4.80/1.91  tff(c_969, plain, (~l1_orders_2('#skF_7') | ~v1_yellow_0('#skF_7') | ~v5_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_40, c_966])).
% 4.80/1.91  tff(c_972, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_969])).
% 4.80/1.91  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_972])).
% 4.80/1.91  tff(c_976, plain, (r1_yellow_0('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_965])).
% 4.80/1.91  tff(c_1354, plain, (![A_307, B_308, D_309]: (r1_orders_2(A_307, k1_yellow_0(A_307, B_308), D_309) | ~r2_lattice3(A_307, B_308, D_309) | ~m1_subset_1(D_309, u1_struct_0(A_307)) | ~r1_yellow_0(A_307, B_308) | ~m1_subset_1(k1_yellow_0(A_307, B_308), u1_struct_0(A_307)) | ~l1_orders_2(A_307))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.80/1.91  tff(c_1361, plain, (![D_309]: (r1_orders_2('#skF_7', k1_yellow_0('#skF_7', k1_xboole_0), D_309) | ~r2_lattice3('#skF_7', k1_xboole_0, D_309) | ~m1_subset_1(D_309, u1_struct_0('#skF_7')) | ~r1_yellow_0('#skF_7', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~l1_orders_2('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1354])).
% 4.80/1.91  tff(c_1367, plain, (![D_309]: (r1_orders_2('#skF_7', k3_yellow_0('#skF_7'), D_309) | ~r2_lattice3('#skF_7', k1_xboole_0, D_309) | ~m1_subset_1(D_309, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_154, c_976, c_96, c_1361])).
% 4.80/1.91  tff(c_1443, plain, (![D_326, B_327, A_328, C_329]: (r2_hidden(D_326, B_327) | ~r1_orders_2(A_328, C_329, D_326) | ~r2_hidden(C_329, B_327) | ~m1_subset_1(D_326, u1_struct_0(A_328)) | ~m1_subset_1(C_329, u1_struct_0(A_328)) | ~v13_waybel_0(B_327, A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_orders_2(A_328))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.80/1.91  tff(c_1451, plain, (![D_309, B_327]: (r2_hidden(D_309, B_327) | ~r2_hidden(k3_yellow_0('#skF_7'), B_327) | ~m1_subset_1(k3_yellow_0('#skF_7'), u1_struct_0('#skF_7')) | ~v13_waybel_0(B_327, '#skF_7') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_309) | ~m1_subset_1(D_309, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_1367, c_1443])).
% 4.80/1.91  tff(c_1483, plain, (![D_330, B_331]: (r2_hidden(D_330, B_331) | ~r2_hidden(k3_yellow_0('#skF_7'), B_331) | ~v13_waybel_0(B_331, '#skF_7') | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r2_lattice3('#skF_7', k1_xboole_0, D_330) | ~m1_subset_1(D_330, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_154, c_1451])).
% 4.80/1.91  tff(c_1491, plain, (![D_330]: (r2_hidden(D_330, '#skF_8') | ~r2_hidden(k3_yellow_0('#skF_7'), '#skF_8') | ~v13_waybel_0('#skF_8', '#skF_7') | ~r2_lattice3('#skF_7', k1_xboole_0, D_330) | ~m1_subset_1(D_330, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_58, c_1483])).
% 4.80/1.91  tff(c_1509, plain, (![D_334]: (r2_hidden(D_334, '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, D_334) | ~m1_subset_1(D_334, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_132, c_1491])).
% 4.80/1.91  tff(c_1614, plain, (![B_337]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_337), '#skF_8') | ~r2_lattice3('#skF_7', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_7'), B_337)) | u1_struct_0('#skF_7')=B_337 | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_10, c_1509])).
% 4.80/1.91  tff(c_1618, plain, (![B_6]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_6), '#skF_8') | ~v1_xboole_0(k1_xboole_0) | ~l1_orders_2('#skF_7') | u1_struct_0('#skF_7')=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(resolution, [status(thm)], [c_230, c_1614])).
% 4.80/1.91  tff(c_1645, plain, (![B_339]: (r2_hidden('#skF_2'(u1_struct_0('#skF_7'), B_339), '#skF_8') | u1_struct_0('#skF_7')=B_339 | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6, c_1618])).
% 4.80/1.91  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | B_6=A_5 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/1.91  tff(c_1655, plain, (u1_struct_0('#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_1645, c_8])).
% 4.80/1.91  tff(c_1664, plain, (u1_struct_0('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1655])).
% 4.80/1.91  tff(c_133, plain, (v1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_78])).
% 4.80/1.91  tff(c_1681, plain, (v1_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_133])).
% 4.80/1.91  tff(c_1682, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_58])).
% 4.80/1.91  tff(c_56, plain, (![B_67]: (~v1_subset_1(B_67, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.80/1.91  tff(c_1780, plain, (~v1_subset_1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_1682, c_56])).
% 4.80/1.91  tff(c_1788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1780])).
% 4.80/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.91  
% 4.80/1.91  Inference rules
% 4.80/1.91  ----------------------
% 4.80/1.91  #Ref     : 0
% 4.80/1.91  #Sup     : 325
% 4.80/1.91  #Fact    : 0
% 4.80/1.91  #Define  : 0
% 4.80/1.91  #Split   : 5
% 4.80/1.91  #Chain   : 0
% 5.14/1.91  #Close   : 0
% 5.14/1.91  
% 5.14/1.91  Ordering : KBO
% 5.14/1.91  
% 5.14/1.91  Simplification rules
% 5.14/1.91  ----------------------
% 5.14/1.91  #Subsume      : 31
% 5.14/1.91  #Demod        : 354
% 5.14/1.91  #Tautology    : 97
% 5.14/1.91  #SimpNegUnit  : 11
% 5.14/1.91  #BackRed      : 38
% 5.14/1.91  
% 5.14/1.91  #Partial instantiations: 0
% 5.14/1.91  #Strategies tried      : 1
% 5.14/1.91  
% 5.14/1.91  Timing (in seconds)
% 5.14/1.91  ----------------------
% 5.14/1.91  Preprocessing        : 0.42
% 5.14/1.91  Parsing              : 0.22
% 5.14/1.91  CNF conversion       : 0.03
% 5.14/1.91  Main loop            : 0.66
% 5.14/1.91  Inferencing          : 0.23
% 5.14/1.91  Reduction            : 0.21
% 5.14/1.91  Demodulation         : 0.15
% 5.14/1.91  BG Simplification    : 0.04
% 5.14/1.91  Subsumption          : 0.12
% 5.14/1.91  Abstraction          : 0.03
% 5.14/1.91  MUC search           : 0.00
% 5.14/1.91  Cooper               : 0.00
% 5.14/1.91  Total                : 1.14
% 5.14/1.91  Index Insertion      : 0.00
% 5.14/1.91  Index Deletion       : 0.00
% 5.14/1.91  Index Matching       : 0.00
% 5.14/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
