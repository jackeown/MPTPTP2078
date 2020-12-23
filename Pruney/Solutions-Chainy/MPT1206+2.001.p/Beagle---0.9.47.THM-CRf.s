%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 9.56s
% Output     : CNFRefutation 9.78s
% Verified   : 
% Statistics : Number of formulae       :  192 (1423 expanded)
%              Number of leaves         :   43 ( 494 expanded)
%              Depth                    :   27
%              Number of atoms          :  545 (5154 expanded)
%              Number of equality atoms :   76 ( 600 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_227,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

tff(f_140,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_176,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(f_193,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,k4_lattices(A,B,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v5_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k1_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k1_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

tff(f_212,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') != k5_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_68,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_75,plain,(
    ! [A_82] :
      ( l1_lattices(A_82)
      | ~ l3_lattices(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_79,plain,(
    l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_48,plain,(
    ! [A_59] :
      ( m1_subset_1(k5_lattices(A_59),u1_struct_0(A_59))
      | ~ l1_lattices(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_70,plain,(
    v13_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_1854,plain,(
    ! [A_218,C_219] :
      ( k2_lattices(A_218,k5_lattices(A_218),C_219) = k5_lattices(A_218)
      | ~ m1_subset_1(C_219,u1_struct_0(A_218))
      | ~ m1_subset_1(k5_lattices(A_218),u1_struct_0(A_218))
      | ~ v13_lattices(A_218)
      | ~ l1_lattices(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1872,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_1854])).

tff(c_1883,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_70,c_1872])).

tff(c_1884,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1883])).

tff(c_1896,plain,(
    ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1884])).

tff(c_1899,plain,
    ( ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1896])).

tff(c_1902,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1899])).

tff(c_1904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1902])).

tff(c_1906,plain,(
    m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1884])).

tff(c_72,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1812,plain,(
    ! [A_215,B_216,C_217] :
      ( r3_lattices(A_215,B_216,B_216)
      | ~ m1_subset_1(C_217,u1_struct_0(A_215))
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l3_lattices(A_215)
      | ~ v9_lattices(A_215)
      | ~ v8_lattices(A_215)
      | ~ v6_lattices(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1830,plain,(
    ! [B_216] :
      ( r3_lattices('#skF_7',B_216,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1812])).

tff(c_1841,plain,(
    ! [B_216] :
      ( r3_lattices('#skF_7',B_216,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1830])).

tff(c_1842,plain,(
    ! [B_216] :
      ( r3_lattices('#skF_7',B_216,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1841])).

tff(c_1843,plain,(
    ~ v6_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_1846,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_1843])).

tff(c_1849,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1846])).

tff(c_1851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1849])).

tff(c_1853,plain,(
    v6_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1852,plain,(
    ! [B_216] :
      ( ~ v8_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | r3_lattices('#skF_7',B_216,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_1885,plain,(
    ~ v9_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1852])).

tff(c_1888,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_1885])).

tff(c_1891,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1888])).

tff(c_1893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1891])).

tff(c_1894,plain,(
    ! [B_216] :
      ( ~ v8_lattices('#skF_7')
      | r3_lattices('#skF_7',B_216,B_216)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1852])).

tff(c_1939,plain,(
    ~ v8_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1894])).

tff(c_1979,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_1939])).

tff(c_1982,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1979])).

tff(c_1984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1982])).

tff(c_1986,plain,(
    v8_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1894])).

tff(c_46,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k4_lattices(A_56,B_57,C_58),u1_struct_0(A_56))
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_lattices(A_56)
      | ~ v6_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_80,plain,(
    ! [A_83] :
      ( l2_lattices(A_83)
      | ~ l3_lattices(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_84,plain,(
    l2_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_100,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_lattices(A_102,B_103,C_104)
      | k1_lattices(A_102,B_103,C_104) != C_104
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l2_lattices(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [B_103] :
      ( r1_lattices('#skF_7',B_103,'#skF_8')
      | k1_lattices('#skF_7',B_103,'#skF_8') != '#skF_8'
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_7'))
      | ~ l2_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_129,plain,(
    ! [B_103] :
      ( r1_lattices('#skF_7',B_103,'#skF_8')
      | k1_lattices('#skF_7',B_103,'#skF_8') != '#skF_8'
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_118])).

tff(c_131,plain,(
    ! [B_105] :
      ( r1_lattices('#skF_7',B_105,'#skF_8')
      | k1_lattices('#skF_7',B_105,'#skF_8') != '#skF_8'
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_129])).

tff(c_163,plain,
    ( r1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') != '#skF_8'
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_131])).

tff(c_197,plain,
    ( r1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') != '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_163])).

tff(c_198,plain,
    ( r1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_197])).

tff(c_1375,plain,(
    k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_1499,plain,(
    ! [A_197,C_198] :
      ( k2_lattices(A_197,k5_lattices(A_197),C_198) = k5_lattices(A_197)
      | ~ m1_subset_1(C_198,u1_struct_0(A_197))
      | ~ m1_subset_1(k5_lattices(A_197),u1_struct_0(A_197))
      | ~ v13_lattices(A_197)
      | ~ l1_lattices(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1517,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_1499])).

tff(c_1528,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_70,c_1517])).

tff(c_1529,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1528])).

tff(c_1593,plain,(
    ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1529])).

tff(c_1596,plain,
    ( ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_1593])).

tff(c_1599,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1596])).

tff(c_1601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1599])).

tff(c_1602,plain,(
    k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1529])).

tff(c_1603,plain,(
    m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1529])).

tff(c_1395,plain,(
    ! [A_190,B_191,C_192] :
      ( r3_lattices(A_190,B_191,B_191)
      | ~ m1_subset_1(C_192,u1_struct_0(A_190))
      | ~ m1_subset_1(B_191,u1_struct_0(A_190))
      | ~ l3_lattices(A_190)
      | ~ v9_lattices(A_190)
      | ~ v8_lattices(A_190)
      | ~ v6_lattices(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1413,plain,(
    ! [B_191] :
      ( r3_lattices('#skF_7',B_191,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1395])).

tff(c_1424,plain,(
    ! [B_191] :
      ( r3_lattices('#skF_7',B_191,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1413])).

tff(c_1425,plain,(
    ! [B_191] :
      ( r3_lattices('#skF_7',B_191,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1424])).

tff(c_1426,plain,(
    ~ v6_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1425])).

tff(c_1460,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_1426])).

tff(c_1463,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1460])).

tff(c_1465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1463])).

tff(c_1466,plain,(
    ! [B_191] :
      ( ~ v8_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | r3_lattices('#skF_7',B_191,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1425])).

tff(c_1468,plain,(
    ~ v9_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1466])).

tff(c_1480,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_1468])).

tff(c_1483,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1480])).

tff(c_1485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1483])).

tff(c_1486,plain,(
    ! [B_191] :
      ( ~ v8_lattices('#skF_7')
      | r3_lattices('#skF_7',B_191,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1466])).

tff(c_1488,plain,(
    ~ v8_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1486])).

tff(c_1491,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_1488])).

tff(c_1494,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1491])).

tff(c_1496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1494])).

tff(c_1498,plain,(
    v8_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1486])).

tff(c_1701,plain,(
    ! [A_207,B_208,C_209] :
      ( k1_lattices(A_207,k2_lattices(A_207,B_208,C_209),C_209) = C_209
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ v8_lattices(A_207)
      | ~ l3_lattices(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1721,plain,(
    ! [B_208] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_208,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_7'))
      | ~ v8_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1701])).

tff(c_1736,plain,(
    ! [B_208] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_208,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1498,c_1721])).

tff(c_1738,plain,(
    ! [B_210] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_210,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_210,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1736])).

tff(c_1741,plain,(
    k1_lattices('#skF_7',k2_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1603,c_1738])).

tff(c_1778,plain,(
    k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_1741])).

tff(c_1780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1375,c_1778])).

tff(c_1782,plain,(
    k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_2342,plain,(
    ! [A_242,B_243,C_244] :
      ( r1_lattices(A_242,k4_lattices(A_242,B_243,C_244),B_243)
      | ~ m1_subset_1(C_244,u1_struct_0(A_242))
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l3_lattices(A_242)
      | ~ v8_lattices(A_242)
      | ~ v6_lattices(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_26,plain,(
    ! [A_12,B_16,C_18] :
      ( k1_lattices(A_12,B_16,C_18) = C_18
      | ~ r1_lattices(A_12,B_16,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_12))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4280,plain,(
    ! [A_397,B_398,C_399] :
      ( k1_lattices(A_397,k4_lattices(A_397,B_398,C_399),B_398) = B_398
      | ~ m1_subset_1(k4_lattices(A_397,B_398,C_399),u1_struct_0(A_397))
      | ~ l2_lattices(A_397)
      | ~ m1_subset_1(C_399,u1_struct_0(A_397))
      | ~ m1_subset_1(B_398,u1_struct_0(A_397))
      | ~ l3_lattices(A_397)
      | ~ v8_lattices(A_397)
      | ~ v6_lattices(A_397)
      | v2_struct_0(A_397) ) ),
    inference(resolution,[status(thm)],[c_2342,c_26])).

tff(c_4284,plain,(
    ! [A_400,B_401,C_402] :
      ( k1_lattices(A_400,k4_lattices(A_400,B_401,C_402),B_401) = B_401
      | ~ l2_lattices(A_400)
      | ~ l3_lattices(A_400)
      | ~ v8_lattices(A_400)
      | ~ m1_subset_1(C_402,u1_struct_0(A_400))
      | ~ m1_subset_1(B_401,u1_struct_0(A_400))
      | ~ l1_lattices(A_400)
      | ~ v6_lattices(A_400)
      | v2_struct_0(A_400) ) ),
    inference(resolution,[status(thm)],[c_46,c_4280])).

tff(c_4304,plain,(
    ! [B_401] :
      ( k1_lattices('#skF_7',k4_lattices('#skF_7',B_401,'#skF_8'),B_401) = B_401
      | ~ l2_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ m1_subset_1(B_401,u1_struct_0('#skF_7'))
      | ~ l1_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_4284])).

tff(c_4319,plain,(
    ! [B_401] :
      ( k1_lattices('#skF_7',k4_lattices('#skF_7',B_401,'#skF_8'),B_401) = B_401
      | ~ m1_subset_1(B_401,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1853,c_79,c_1986,c_68,c_84,c_4304])).

tff(c_4321,plain,(
    ! [B_403] :
      ( k1_lattices('#skF_7',k4_lattices('#skF_7',B_403,'#skF_8'),B_403) = B_403
      | ~ m1_subset_1(B_403,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4319])).

tff(c_4347,plain,
    ( k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),k5_lattices('#skF_7')) = k5_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_4321])).

tff(c_4381,plain,
    ( k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),k5_lattices('#skF_7')) = k5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_4347])).

tff(c_4382,plain,(
    k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),k5_lattices('#skF_7')) = k5_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4381])).

tff(c_36,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_2'(A_19),u1_struct_0(A_19))
      | v5_lattices(A_19)
      | ~ l2_lattices(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1987,plain,(
    ! [B_223] :
      ( r3_lattices('#skF_7',B_223,B_223)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_1894])).

tff(c_2004,plain,
    ( r3_lattices('#skF_7','#skF_2'('#skF_7'),'#skF_2'('#skF_7'))
    | v5_lattices('#skF_7')
    | ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1987])).

tff(c_2035,plain,
    ( r3_lattices('#skF_7','#skF_2'('#skF_7'),'#skF_2'('#skF_7'))
    | v5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2004])).

tff(c_2036,plain,
    ( r3_lattices('#skF_7','#skF_2'('#skF_7'),'#skF_2'('#skF_7'))
    | v5_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2035])).

tff(c_2051,plain,(
    v5_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2036])).

tff(c_3038,plain,(
    ! [A_307,B_308,C_309,D_310] :
      ( k1_lattices(A_307,k1_lattices(A_307,B_308,C_309),D_310) = k1_lattices(A_307,B_308,k1_lattices(A_307,C_309,D_310))
      | ~ m1_subset_1(D_310,u1_struct_0(A_307))
      | ~ m1_subset_1(C_309,u1_struct_0(A_307))
      | ~ m1_subset_1(B_308,u1_struct_0(A_307))
      | ~ v5_lattices(A_307)
      | ~ l2_lattices(A_307)
      | v2_struct_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3058,plain,(
    ! [B_308,C_309] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_308,C_309),'#skF_8') = k1_lattices('#skF_7',B_308,k1_lattices('#skF_7',C_309,'#skF_8'))
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_7'))
      | ~ v5_lattices('#skF_7')
      | ~ l2_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_3038])).

tff(c_3073,plain,(
    ! [B_308,C_309] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_308,C_309),'#skF_8') = k1_lattices('#skF_7',B_308,k1_lattices('#skF_7',C_309,'#skF_8'))
      | ~ m1_subset_1(C_309,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2051,c_3058])).

tff(c_3094,plain,(
    ! [B_312,C_313] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_312,C_313),'#skF_8') = k1_lattices('#skF_7',B_312,k1_lattices('#skF_7',C_313,'#skF_8'))
      | ~ m1_subset_1(C_313,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3073])).

tff(c_3120,plain,(
    ! [B_312] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_312,k5_lattices('#skF_7')),'#skF_8') = k1_lattices('#skF_7',B_312,k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'))
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_7'))
      | ~ l1_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_3094])).

tff(c_3155,plain,(
    ! [B_312] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_312,k5_lattices('#skF_7')),'#skF_8') = k1_lattices('#skF_7',B_312,'#skF_8')
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1782,c_3120])).

tff(c_3156,plain,(
    ! [B_312] :
      ( k1_lattices('#skF_7',k1_lattices('#skF_7',B_312,k5_lattices('#skF_7')),'#skF_8') = k1_lattices('#skF_7',B_312,'#skF_8')
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3155])).

tff(c_4413,plain,
    ( k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),'#skF_8') = k1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | ~ m1_subset_1(k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4382,c_3156])).

tff(c_4421,plain,
    ( k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),'#skF_8') = '#skF_8'
    | ~ m1_subset_1(k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1782,c_4413])).

tff(c_4490,plain,(
    ~ m1_subset_1(k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4421])).

tff(c_4493,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_4490])).

tff(c_4496,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1853,c_79,c_1906,c_66,c_4493])).

tff(c_4498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4496])).

tff(c_4500,plain,(
    m1_subset_1(k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4421])).

tff(c_22,plain,(
    ! [A_2,C_11] :
      ( k2_lattices(A_2,k5_lattices(A_2),C_11) = k5_lattices(A_2)
      | ~ m1_subset_1(C_11,u1_struct_0(A_2))
      | ~ m1_subset_1(k5_lattices(A_2),u1_struct_0(A_2))
      | ~ v13_lattices(A_2)
      | ~ l1_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4720,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k5_lattices('#skF_7')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v13_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4500,c_22])).

tff(c_4768,plain,
    ( k2_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_70,c_1906,c_4720])).

tff(c_4769,plain,(
    k2_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k5_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4768])).

tff(c_2139,plain,(
    ! [A_232,B_233,C_234] :
      ( k1_lattices(A_232,k2_lattices(A_232,B_233,C_234),C_234) = C_234
      | ~ m1_subset_1(C_234,u1_struct_0(A_232))
      | ~ m1_subset_1(B_233,u1_struct_0(A_232))
      | ~ v8_lattices(A_232)
      | ~ l3_lattices(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6338,plain,(
    ! [A_436,B_437,B_438,C_439] :
      ( k1_lattices(A_436,k2_lattices(A_436,B_437,k4_lattices(A_436,B_438,C_439)),k4_lattices(A_436,B_438,C_439)) = k4_lattices(A_436,B_438,C_439)
      | ~ m1_subset_1(B_437,u1_struct_0(A_436))
      | ~ v8_lattices(A_436)
      | ~ l3_lattices(A_436)
      | ~ m1_subset_1(C_439,u1_struct_0(A_436))
      | ~ m1_subset_1(B_438,u1_struct_0(A_436))
      | ~ l1_lattices(A_436)
      | ~ v6_lattices(A_436)
      | v2_struct_0(A_436) ) ),
    inference(resolution,[status(thm)],[c_46,c_2139])).

tff(c_6363,plain,
    ( k1_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v8_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4769,c_6338])).

tff(c_6379,plain,
    ( k1_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1853,c_79,c_1906,c_66,c_68,c_1986,c_1906,c_6363])).

tff(c_6380,plain,(
    k1_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) = k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6379])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1781,plain,(
    r1_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_2408,plain,(
    ! [C_259,B_260,A_261] :
      ( C_259 = B_260
      | ~ r1_lattices(A_261,C_259,B_260)
      | ~ r1_lattices(A_261,B_260,C_259)
      | ~ m1_subset_1(C_259,u1_struct_0(A_261))
      | ~ m1_subset_1(B_260,u1_struct_0(A_261))
      | ~ l2_lattices(A_261)
      | ~ v4_lattices(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2424,plain,
    ( k5_lattices('#skF_7') = '#skF_8'
    | ~ r1_lattices('#skF_7','#skF_8',k5_lattices('#skF_7'))
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l2_lattices('#skF_7')
    | ~ v4_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1781,c_2408])).

tff(c_2445,plain,
    ( k5_lattices('#skF_7') = '#skF_8'
    | ~ r1_lattices('#skF_7','#skF_8',k5_lattices('#skF_7'))
    | ~ v4_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_66,c_1906,c_2424])).

tff(c_2446,plain,
    ( k5_lattices('#skF_7') = '#skF_8'
    | ~ r1_lattices('#skF_7','#skF_8',k5_lattices('#skF_7'))
    | ~ v4_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2445])).

tff(c_2452,plain,(
    ~ v4_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2446])).

tff(c_2455,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2452])).

tff(c_2458,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_2455])).

tff(c_2460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2458])).

tff(c_2462,plain,(
    v4_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2446])).

tff(c_24,plain,(
    ! [A_12,B_16,C_18] :
      ( r1_lattices(A_12,B_16,C_18)
      | k1_lattices(A_12,B_16,C_18) != C_18
      | ~ m1_subset_1(C_18,u1_struct_0(A_12))
      | ~ m1_subset_1(B_16,u1_struct_0(A_12))
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4727,plain,(
    ! [B_16] :
      ( r1_lattices('#skF_7',B_16,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'))
      | k1_lattices('#skF_7',B_16,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) != k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_7'))
      | ~ l2_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4500,c_24])).

tff(c_4777,plain,(
    ! [B_16] :
      ( r1_lattices('#skF_7',B_16,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'))
      | k1_lattices('#skF_7',B_16,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) != k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
      | ~ m1_subset_1(B_16,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4727])).

tff(c_10550,plain,(
    ! [B_486] :
      ( r1_lattices('#skF_7',B_486,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'))
      | k1_lattices('#skF_7',B_486,k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) != k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4777])).

tff(c_2599,plain,(
    ! [A_269,B_270] :
      ( r1_lattices(A_269,B_270,k5_lattices(A_269))
      | k1_lattices(A_269,B_270,k5_lattices(A_269)) != k5_lattices(A_269)
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l2_lattices(A_269)
      | ~ l1_lattices(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_62,plain,(
    ! [C_80,B_78,A_74] :
      ( C_80 = B_78
      | ~ r1_lattices(A_74,C_80,B_78)
      | ~ r1_lattices(A_74,B_78,C_80)
      | ~ m1_subset_1(C_80,u1_struct_0(A_74))
      | ~ m1_subset_1(B_78,u1_struct_0(A_74))
      | ~ l2_lattices(A_74)
      | ~ v4_lattices(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2620,plain,(
    ! [A_269,B_270] :
      ( k5_lattices(A_269) = B_270
      | ~ r1_lattices(A_269,k5_lattices(A_269),B_270)
      | ~ m1_subset_1(k5_lattices(A_269),u1_struct_0(A_269))
      | ~ v4_lattices(A_269)
      | k1_lattices(A_269,B_270,k5_lattices(A_269)) != k5_lattices(A_269)
      | ~ m1_subset_1(B_270,u1_struct_0(A_269))
      | ~ l2_lattices(A_269)
      | ~ l1_lattices(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_2599,c_62])).

tff(c_10562,plain,
    ( k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | ~ v4_lattices('#skF_7')
    | k1_lattices('#skF_7',k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),k5_lattices('#skF_7')) != k5_lattices('#skF_7')
    | ~ m1_subset_1(k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l2_lattices('#skF_7')
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | k1_lattices('#skF_7',k5_lattices('#skF_7'),k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')) != k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8')
    | ~ m1_subset_1(k5_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_10550,c_2620])).

tff(c_10597,plain,
    ( k4_lattices('#skF_7',k5_lattices('#skF_7'),'#skF_8') = k5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1906,c_6380,c_79,c_84,c_4500,c_4382,c_2462,c_10562])).

tff(c_10599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64,c_10597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.56/3.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.56/3.60  
% 9.56/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.56/3.60  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_6
% 9.56/3.60  
% 9.56/3.60  %Foreground sorts:
% 9.56/3.60  
% 9.56/3.60  
% 9.56/3.60  %Background operators:
% 9.56/3.60  
% 9.56/3.60  
% 9.56/3.60  %Foreground operators:
% 9.56/3.60  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.56/3.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.56/3.60  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 9.56/3.60  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.56/3.60  tff(l2_lattices, type, l2_lattices: $i > $o).
% 9.56/3.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.56/3.60  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.56/3.60  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 9.56/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.56/3.60  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 9.56/3.60  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 9.56/3.60  tff(l1_lattices, type, l1_lattices: $i > $o).
% 9.56/3.60  tff('#skF_7', type, '#skF_7': $i).
% 9.56/3.60  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.56/3.60  tff(v4_lattices, type, v4_lattices: $i > $o).
% 9.56/3.60  tff(v6_lattices, type, v6_lattices: $i > $o).
% 9.56/3.60  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.56/3.60  tff(v5_lattices, type, v5_lattices: $i > $o).
% 9.56/3.60  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.56/3.60  tff('#skF_8', type, '#skF_8': $i).
% 9.56/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.56/3.60  tff(v13_lattices, type, v13_lattices: $i > $o).
% 9.56/3.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.56/3.60  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.56/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.56/3.60  tff(k5_lattices, type, k5_lattices: $i > $i).
% 9.56/3.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.56/3.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.56/3.60  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.56/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.56/3.60  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.56/3.60  
% 9.78/3.63  tff(f_227, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 9.78/3.63  tff(f_140, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 9.78/3.63  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 9.78/3.63  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattices)).
% 9.78/3.63  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 9.78/3.63  tff(f_176, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_lattices(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 9.78/3.63  tff(f_127, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_lattices)).
% 9.78/3.63  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 9.78/3.63  tff(f_114, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 9.78/3.63  tff(f_193, axiom, (![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 9.78/3.63  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v5_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k1_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k1_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattices)).
% 9.78/3.63  tff(f_212, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 9.78/3.63  tff(c_74, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_64, plain, (k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')!=k5_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_68, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_75, plain, (![A_82]: (l1_lattices(A_82) | ~l3_lattices(A_82))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.78/3.63  tff(c_79, plain, (l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_68, c_75])).
% 9.78/3.63  tff(c_48, plain, (![A_59]: (m1_subset_1(k5_lattices(A_59), u1_struct_0(A_59)) | ~l1_lattices(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.78/3.63  tff(c_70, plain, (v13_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_1854, plain, (![A_218, C_219]: (k2_lattices(A_218, k5_lattices(A_218), C_219)=k5_lattices(A_218) | ~m1_subset_1(C_219, u1_struct_0(A_218)) | ~m1_subset_1(k5_lattices(A_218), u1_struct_0(A_218)) | ~v13_lattices(A_218) | ~l1_lattices(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.78/3.63  tff(c_1872, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_1854])).
% 9.78/3.63  tff(c_1883, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_70, c_1872])).
% 9.78/3.63  tff(c_1884, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1883])).
% 9.78/3.63  tff(c_1896, plain, (~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_1884])).
% 9.78/3.63  tff(c_1899, plain, (~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1896])).
% 9.78/3.63  tff(c_1902, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1899])).
% 9.78/3.63  tff(c_1904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1902])).
% 9.78/3.63  tff(c_1906, plain, (m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_1884])).
% 9.78/3.63  tff(c_72, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.78/3.63  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.63  tff(c_1812, plain, (![A_215, B_216, C_217]: (r3_lattices(A_215, B_216, B_216) | ~m1_subset_1(C_217, u1_struct_0(A_215)) | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l3_lattices(A_215) | ~v9_lattices(A_215) | ~v8_lattices(A_215) | ~v6_lattices(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.78/3.63  tff(c_1830, plain, (![B_216]: (r3_lattices('#skF_7', B_216, B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1812])).
% 9.78/3.63  tff(c_1841, plain, (![B_216]: (r3_lattices('#skF_7', B_216, B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1830])).
% 9.78/3.63  tff(c_1842, plain, (![B_216]: (r3_lattices('#skF_7', B_216, B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1841])).
% 9.78/3.63  tff(c_1843, plain, (~v6_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1842])).
% 9.78/3.63  tff(c_1846, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_8, c_1843])).
% 9.78/3.63  tff(c_1849, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1846])).
% 9.78/3.63  tff(c_1851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1849])).
% 9.78/3.63  tff(c_1853, plain, (v6_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_1842])).
% 9.78/3.63  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.63  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.63  tff(c_1852, plain, (![B_216]: (~v8_lattices('#skF_7') | ~v9_lattices('#skF_7') | r3_lattices('#skF_7', B_216, B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_1842])).
% 9.78/3.63  tff(c_1885, plain, (~v9_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1852])).
% 9.78/3.63  tff(c_1888, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_2, c_1885])).
% 9.78/3.63  tff(c_1891, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1888])).
% 9.78/3.63  tff(c_1893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1891])).
% 9.78/3.63  tff(c_1894, plain, (![B_216]: (~v8_lattices('#skF_7') | r3_lattices('#skF_7', B_216, B_216) | ~m1_subset_1(B_216, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_1852])).
% 9.78/3.63  tff(c_1939, plain, (~v8_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1894])).
% 9.78/3.63  tff(c_1979, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_4, c_1939])).
% 9.78/3.63  tff(c_1982, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1979])).
% 9.78/3.63  tff(c_1984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1982])).
% 9.78/3.63  tff(c_1986, plain, (v8_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_1894])).
% 9.78/3.63  tff(c_46, plain, (![A_56, B_57, C_58]: (m1_subset_1(k4_lattices(A_56, B_57, C_58), u1_struct_0(A_56)) | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_lattices(A_56) | ~v6_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.78/3.63  tff(c_80, plain, (![A_83]: (l2_lattices(A_83) | ~l3_lattices(A_83))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.78/3.63  tff(c_84, plain, (l2_lattices('#skF_7')), inference(resolution, [status(thm)], [c_68, c_80])).
% 9.78/3.63  tff(c_100, plain, (![A_102, B_103, C_104]: (r1_lattices(A_102, B_103, C_104) | k1_lattices(A_102, B_103, C_104)!=C_104 | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l2_lattices(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.78/3.63  tff(c_118, plain, (![B_103]: (r1_lattices('#skF_7', B_103, '#skF_8') | k1_lattices('#skF_7', B_103, '#skF_8')!='#skF_8' | ~m1_subset_1(B_103, u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_100])).
% 9.78/3.63  tff(c_129, plain, (![B_103]: (r1_lattices('#skF_7', B_103, '#skF_8') | k1_lattices('#skF_7', B_103, '#skF_8')!='#skF_8' | ~m1_subset_1(B_103, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_118])).
% 9.78/3.63  tff(c_131, plain, (![B_105]: (r1_lattices('#skF_7', B_105, '#skF_8') | k1_lattices('#skF_7', B_105, '#skF_8')!='#skF_8' | ~m1_subset_1(B_105, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_129])).
% 9.78/3.63  tff(c_163, plain, (r1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')!='#skF_8' | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_131])).
% 9.78/3.63  tff(c_197, plain, (r1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')!='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_163])).
% 9.78/3.63  tff(c_198, plain, (r1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_74, c_197])).
% 9.78/3.63  tff(c_1375, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')!='#skF_8'), inference(splitLeft, [status(thm)], [c_198])).
% 9.78/3.63  tff(c_1499, plain, (![A_197, C_198]: (k2_lattices(A_197, k5_lattices(A_197), C_198)=k5_lattices(A_197) | ~m1_subset_1(C_198, u1_struct_0(A_197)) | ~m1_subset_1(k5_lattices(A_197), u1_struct_0(A_197)) | ~v13_lattices(A_197) | ~l1_lattices(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.78/3.63  tff(c_1517, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_1499])).
% 9.78/3.63  tff(c_1528, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_70, c_1517])).
% 9.78/3.63  tff(c_1529, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1528])).
% 9.78/3.63  tff(c_1593, plain, (~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_1529])).
% 9.78/3.63  tff(c_1596, plain, (~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_1593])).
% 9.78/3.63  tff(c_1599, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1596])).
% 9.78/3.63  tff(c_1601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1599])).
% 9.78/3.63  tff(c_1602, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_1529])).
% 9.78/3.63  tff(c_1603, plain, (m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_1529])).
% 9.78/3.63  tff(c_1395, plain, (![A_190, B_191, C_192]: (r3_lattices(A_190, B_191, B_191) | ~m1_subset_1(C_192, u1_struct_0(A_190)) | ~m1_subset_1(B_191, u1_struct_0(A_190)) | ~l3_lattices(A_190) | ~v9_lattices(A_190) | ~v8_lattices(A_190) | ~v6_lattices(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.78/3.63  tff(c_1413, plain, (![B_191]: (r3_lattices('#skF_7', B_191, B_191) | ~m1_subset_1(B_191, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1395])).
% 9.78/3.63  tff(c_1424, plain, (![B_191]: (r3_lattices('#skF_7', B_191, B_191) | ~m1_subset_1(B_191, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1413])).
% 9.78/3.63  tff(c_1425, plain, (![B_191]: (r3_lattices('#skF_7', B_191, B_191) | ~m1_subset_1(B_191, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1424])).
% 9.78/3.63  tff(c_1426, plain, (~v6_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1425])).
% 9.78/3.63  tff(c_1460, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_8, c_1426])).
% 9.78/3.63  tff(c_1463, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1460])).
% 9.78/3.63  tff(c_1465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1463])).
% 9.78/3.63  tff(c_1466, plain, (![B_191]: (~v8_lattices('#skF_7') | ~v9_lattices('#skF_7') | r3_lattices('#skF_7', B_191, B_191) | ~m1_subset_1(B_191, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_1425])).
% 9.78/3.63  tff(c_1468, plain, (~v9_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1466])).
% 9.78/3.63  tff(c_1480, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_2, c_1468])).
% 9.78/3.63  tff(c_1483, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1480])).
% 9.78/3.63  tff(c_1485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1483])).
% 9.78/3.63  tff(c_1486, plain, (![B_191]: (~v8_lattices('#skF_7') | r3_lattices('#skF_7', B_191, B_191) | ~m1_subset_1(B_191, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_1466])).
% 9.78/3.63  tff(c_1488, plain, (~v8_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_1486])).
% 9.78/3.63  tff(c_1491, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_4, c_1488])).
% 9.78/3.63  tff(c_1494, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1491])).
% 9.78/3.63  tff(c_1496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1494])).
% 9.78/3.63  tff(c_1498, plain, (v8_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_1486])).
% 9.78/3.63  tff(c_1701, plain, (![A_207, B_208, C_209]: (k1_lattices(A_207, k2_lattices(A_207, B_208, C_209), C_209)=C_209 | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~v8_lattices(A_207) | ~l3_lattices(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.78/3.63  tff(c_1721, plain, (![B_208]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_208, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_208, u1_struct_0('#skF_7')) | ~v8_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1701])).
% 9.78/3.63  tff(c_1736, plain, (![B_208]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_208, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_208, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1498, c_1721])).
% 9.78/3.63  tff(c_1738, plain, (![B_210]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_210, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_210, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1736])).
% 9.78/3.63  tff(c_1741, plain, (k1_lattices('#skF_7', k2_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1603, c_1738])).
% 9.78/3.63  tff(c_1778, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1602, c_1741])).
% 9.78/3.63  tff(c_1780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1375, c_1778])).
% 9.78/3.63  tff(c_1782, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_198])).
% 9.78/3.63  tff(c_2342, plain, (![A_242, B_243, C_244]: (r1_lattices(A_242, k4_lattices(A_242, B_243, C_244), B_243) | ~m1_subset_1(C_244, u1_struct_0(A_242)) | ~m1_subset_1(B_243, u1_struct_0(A_242)) | ~l3_lattices(A_242) | ~v8_lattices(A_242) | ~v6_lattices(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.78/3.63  tff(c_26, plain, (![A_12, B_16, C_18]: (k1_lattices(A_12, B_16, C_18)=C_18 | ~r1_lattices(A_12, B_16, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_12)) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.78/3.63  tff(c_4280, plain, (![A_397, B_398, C_399]: (k1_lattices(A_397, k4_lattices(A_397, B_398, C_399), B_398)=B_398 | ~m1_subset_1(k4_lattices(A_397, B_398, C_399), u1_struct_0(A_397)) | ~l2_lattices(A_397) | ~m1_subset_1(C_399, u1_struct_0(A_397)) | ~m1_subset_1(B_398, u1_struct_0(A_397)) | ~l3_lattices(A_397) | ~v8_lattices(A_397) | ~v6_lattices(A_397) | v2_struct_0(A_397))), inference(resolution, [status(thm)], [c_2342, c_26])).
% 9.78/3.63  tff(c_4284, plain, (![A_400, B_401, C_402]: (k1_lattices(A_400, k4_lattices(A_400, B_401, C_402), B_401)=B_401 | ~l2_lattices(A_400) | ~l3_lattices(A_400) | ~v8_lattices(A_400) | ~m1_subset_1(C_402, u1_struct_0(A_400)) | ~m1_subset_1(B_401, u1_struct_0(A_400)) | ~l1_lattices(A_400) | ~v6_lattices(A_400) | v2_struct_0(A_400))), inference(resolution, [status(thm)], [c_46, c_4280])).
% 9.78/3.63  tff(c_4304, plain, (![B_401]: (k1_lattices('#skF_7', k4_lattices('#skF_7', B_401, '#skF_8'), B_401)=B_401 | ~l2_lattices('#skF_7') | ~l3_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~m1_subset_1(B_401, u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_4284])).
% 9.78/3.63  tff(c_4319, plain, (![B_401]: (k1_lattices('#skF_7', k4_lattices('#skF_7', B_401, '#skF_8'), B_401)=B_401 | ~m1_subset_1(B_401, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1853, c_79, c_1986, c_68, c_84, c_4304])).
% 9.78/3.63  tff(c_4321, plain, (![B_403]: (k1_lattices('#skF_7', k4_lattices('#skF_7', B_403, '#skF_8'), B_403)=B_403 | ~m1_subset_1(B_403, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_4319])).
% 9.78/3.63  tff(c_4347, plain, (k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), k5_lattices('#skF_7'))=k5_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_4321])).
% 9.78/3.63  tff(c_4381, plain, (k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), k5_lattices('#skF_7'))=k5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_4347])).
% 9.78/3.63  tff(c_4382, plain, (k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), k5_lattices('#skF_7'))=k5_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_4381])).
% 9.78/3.63  tff(c_36, plain, (![A_19]: (m1_subset_1('#skF_2'(A_19), u1_struct_0(A_19)) | v5_lattices(A_19) | ~l2_lattices(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.78/3.63  tff(c_1987, plain, (![B_223]: (r3_lattices('#skF_7', B_223, B_223) | ~m1_subset_1(B_223, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_1894])).
% 9.78/3.63  tff(c_2004, plain, (r3_lattices('#skF_7', '#skF_2'('#skF_7'), '#skF_2'('#skF_7')) | v5_lattices('#skF_7') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_36, c_1987])).
% 9.78/3.63  tff(c_2035, plain, (r3_lattices('#skF_7', '#skF_2'('#skF_7'), '#skF_2'('#skF_7')) | v5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2004])).
% 9.78/3.63  tff(c_2036, plain, (r3_lattices('#skF_7', '#skF_2'('#skF_7'), '#skF_2'('#skF_7')) | v5_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_2035])).
% 9.78/3.63  tff(c_2051, plain, (v5_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_2036])).
% 9.78/3.63  tff(c_3038, plain, (![A_307, B_308, C_309, D_310]: (k1_lattices(A_307, k1_lattices(A_307, B_308, C_309), D_310)=k1_lattices(A_307, B_308, k1_lattices(A_307, C_309, D_310)) | ~m1_subset_1(D_310, u1_struct_0(A_307)) | ~m1_subset_1(C_309, u1_struct_0(A_307)) | ~m1_subset_1(B_308, u1_struct_0(A_307)) | ~v5_lattices(A_307) | ~l2_lattices(A_307) | v2_struct_0(A_307))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.78/3.63  tff(c_3058, plain, (![B_308, C_309]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_308, C_309), '#skF_8')=k1_lattices('#skF_7', B_308, k1_lattices('#skF_7', C_309, '#skF_8')) | ~m1_subset_1(C_309, u1_struct_0('#skF_7')) | ~m1_subset_1(B_308, u1_struct_0('#skF_7')) | ~v5_lattices('#skF_7') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_3038])).
% 9.78/3.63  tff(c_3073, plain, (![B_308, C_309]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_308, C_309), '#skF_8')=k1_lattices('#skF_7', B_308, k1_lattices('#skF_7', C_309, '#skF_8')) | ~m1_subset_1(C_309, u1_struct_0('#skF_7')) | ~m1_subset_1(B_308, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2051, c_3058])).
% 9.78/3.63  tff(c_3094, plain, (![B_312, C_313]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_312, C_313), '#skF_8')=k1_lattices('#skF_7', B_312, k1_lattices('#skF_7', C_313, '#skF_8')) | ~m1_subset_1(C_313, u1_struct_0('#skF_7')) | ~m1_subset_1(B_312, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_3073])).
% 9.78/3.63  tff(c_3120, plain, (![B_312]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_312, k5_lattices('#skF_7')), '#skF_8')=k1_lattices('#skF_7', B_312, k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')) | ~m1_subset_1(B_312, u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_3094])).
% 9.78/3.63  tff(c_3155, plain, (![B_312]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_312, k5_lattices('#skF_7')), '#skF_8')=k1_lattices('#skF_7', B_312, '#skF_8') | ~m1_subset_1(B_312, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1782, c_3120])).
% 9.78/3.63  tff(c_3156, plain, (![B_312]: (k1_lattices('#skF_7', k1_lattices('#skF_7', B_312, k5_lattices('#skF_7')), '#skF_8')=k1_lattices('#skF_7', B_312, '#skF_8') | ~m1_subset_1(B_312, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_3155])).
% 9.78/3.63  tff(c_4413, plain, (k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), '#skF_8')=k1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4382, c_3156])).
% 9.78/3.63  tff(c_4421, plain, (k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1782, c_4413])).
% 9.78/3.63  tff(c_4490, plain, (~m1_subset_1(k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_4421])).
% 9.78/3.63  tff(c_4493, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_46, c_4490])).
% 9.78/3.63  tff(c_4496, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1853, c_79, c_1906, c_66, c_4493])).
% 9.78/3.63  tff(c_4498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4496])).
% 9.78/3.63  tff(c_4500, plain, (m1_subset_1(k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_4421])).
% 9.78/3.63  tff(c_22, plain, (![A_2, C_11]: (k2_lattices(A_2, k5_lattices(A_2), C_11)=k5_lattices(A_2) | ~m1_subset_1(C_11, u1_struct_0(A_2)) | ~m1_subset_1(k5_lattices(A_2), u1_struct_0(A_2)) | ~v13_lattices(A_2) | ~l1_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.78/3.63  tff(c_4720, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k5_lattices('#skF_7') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v13_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4500, c_22])).
% 9.78/3.63  tff(c_4768, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_70, c_1906, c_4720])).
% 9.78/3.63  tff(c_4769, plain, (k2_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k5_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_4768])).
% 9.78/3.63  tff(c_2139, plain, (![A_232, B_233, C_234]: (k1_lattices(A_232, k2_lattices(A_232, B_233, C_234), C_234)=C_234 | ~m1_subset_1(C_234, u1_struct_0(A_232)) | ~m1_subset_1(B_233, u1_struct_0(A_232)) | ~v8_lattices(A_232) | ~l3_lattices(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.78/3.63  tff(c_6338, plain, (![A_436, B_437, B_438, C_439]: (k1_lattices(A_436, k2_lattices(A_436, B_437, k4_lattices(A_436, B_438, C_439)), k4_lattices(A_436, B_438, C_439))=k4_lattices(A_436, B_438, C_439) | ~m1_subset_1(B_437, u1_struct_0(A_436)) | ~v8_lattices(A_436) | ~l3_lattices(A_436) | ~m1_subset_1(C_439, u1_struct_0(A_436)) | ~m1_subset_1(B_438, u1_struct_0(A_436)) | ~l1_lattices(A_436) | ~v6_lattices(A_436) | v2_struct_0(A_436))), inference(resolution, [status(thm)], [c_46, c_2139])).
% 9.78/3.63  tff(c_6363, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v8_lattices('#skF_7') | ~l3_lattices('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4769, c_6338])).
% 9.78/3.63  tff(c_6379, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1853, c_79, c_1906, c_66, c_68, c_1986, c_1906, c_6363])).
% 9.78/3.63  tff(c_6380, plain, (k1_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_6379])).
% 9.78/3.63  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.78/3.63  tff(c_1781, plain, (r1_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_198])).
% 9.78/3.63  tff(c_2408, plain, (![C_259, B_260, A_261]: (C_259=B_260 | ~r1_lattices(A_261, C_259, B_260) | ~r1_lattices(A_261, B_260, C_259) | ~m1_subset_1(C_259, u1_struct_0(A_261)) | ~m1_subset_1(B_260, u1_struct_0(A_261)) | ~l2_lattices(A_261) | ~v4_lattices(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.78/3.63  tff(c_2424, plain, (k5_lattices('#skF_7')='#skF_8' | ~r1_lattices('#skF_7', '#skF_8', k5_lattices('#skF_7')) | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | ~v4_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1781, c_2408])).
% 9.78/3.63  tff(c_2445, plain, (k5_lattices('#skF_7')='#skF_8' | ~r1_lattices('#skF_7', '#skF_8', k5_lattices('#skF_7')) | ~v4_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_66, c_1906, c_2424])).
% 9.78/3.63  tff(c_2446, plain, (k5_lattices('#skF_7')='#skF_8' | ~r1_lattices('#skF_7', '#skF_8', k5_lattices('#skF_7')) | ~v4_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_2445])).
% 9.78/3.63  tff(c_2452, plain, (~v4_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_2446])).
% 9.78/3.63  tff(c_2455, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2452])).
% 9.78/3.63  tff(c_2458, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_2455])).
% 9.78/3.63  tff(c_2460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2458])).
% 9.78/3.63  tff(c_2462, plain, (v4_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_2446])).
% 9.78/3.63  tff(c_24, plain, (![A_12, B_16, C_18]: (r1_lattices(A_12, B_16, C_18) | k1_lattices(A_12, B_16, C_18)!=C_18 | ~m1_subset_1(C_18, u1_struct_0(A_12)) | ~m1_subset_1(B_16, u1_struct_0(A_12)) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.78/3.63  tff(c_4727, plain, (![B_16]: (r1_lattices('#skF_7', B_16, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')) | k1_lattices('#skF_7', B_16, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))!=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(B_16, u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4500, c_24])).
% 9.78/3.63  tff(c_4777, plain, (![B_16]: (r1_lattices('#skF_7', B_16, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')) | k1_lattices('#skF_7', B_16, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))!=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(B_16, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4727])).
% 9.78/3.63  tff(c_10550, plain, (![B_486]: (r1_lattices('#skF_7', B_486, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')) | k1_lattices('#skF_7', B_486, k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))!=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(B_486, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_4777])).
% 9.78/3.63  tff(c_2599, plain, (![A_269, B_270]: (r1_lattices(A_269, B_270, k5_lattices(A_269)) | k1_lattices(A_269, B_270, k5_lattices(A_269))!=k5_lattices(A_269) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l2_lattices(A_269) | ~l1_lattices(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_48, c_100])).
% 9.78/3.63  tff(c_62, plain, (![C_80, B_78, A_74]: (C_80=B_78 | ~r1_lattices(A_74, C_80, B_78) | ~r1_lattices(A_74, B_78, C_80) | ~m1_subset_1(C_80, u1_struct_0(A_74)) | ~m1_subset_1(B_78, u1_struct_0(A_74)) | ~l2_lattices(A_74) | ~v4_lattices(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.78/3.63  tff(c_2620, plain, (![A_269, B_270]: (k5_lattices(A_269)=B_270 | ~r1_lattices(A_269, k5_lattices(A_269), B_270) | ~m1_subset_1(k5_lattices(A_269), u1_struct_0(A_269)) | ~v4_lattices(A_269) | k1_lattices(A_269, B_270, k5_lattices(A_269))!=k5_lattices(A_269) | ~m1_subset_1(B_270, u1_struct_0(A_269)) | ~l2_lattices(A_269) | ~l1_lattices(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_2599, c_62])).
% 9.78/3.63  tff(c_10562, plain, (k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | ~v4_lattices('#skF_7') | k1_lattices('#skF_7', k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), k5_lattices('#skF_7'))!=k5_lattices('#skF_7') | ~m1_subset_1(k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7') | k1_lattices('#skF_7', k5_lattices('#skF_7'), k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8'))!=k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8') | ~m1_subset_1(k5_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_10550, c_2620])).
% 9.78/3.63  tff(c_10597, plain, (k4_lattices('#skF_7', k5_lattices('#skF_7'), '#skF_8')=k5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1906, c_6380, c_79, c_84, c_4500, c_4382, c_2462, c_10562])).
% 9.78/3.63  tff(c_10599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_64, c_10597])).
% 9.78/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.78/3.63  
% 9.78/3.63  Inference rules
% 9.78/3.63  ----------------------
% 9.78/3.63  #Ref     : 0
% 9.78/3.63  #Sup     : 2051
% 9.78/3.63  #Fact    : 0
% 9.78/3.63  #Define  : 0
% 9.78/3.63  #Split   : 67
% 9.78/3.63  #Chain   : 0
% 9.78/3.63  #Close   : 0
% 9.78/3.63  
% 9.78/3.63  Ordering : KBO
% 9.78/3.63  
% 9.78/3.63  Simplification rules
% 9.78/3.63  ----------------------
% 9.78/3.63  #Subsume      : 121
% 9.78/3.63  #Demod        : 4514
% 9.78/3.63  #Tautology    : 1018
% 9.78/3.63  #SimpNegUnit  : 925
% 9.78/3.63  #BackRed      : 0
% 9.78/3.63  
% 9.78/3.63  #Partial instantiations: 0
% 9.78/3.63  #Strategies tried      : 1
% 9.78/3.63  
% 9.78/3.63  Timing (in seconds)
% 9.78/3.63  ----------------------
% 9.78/3.63  Preprocessing        : 0.38
% 9.78/3.63  Parsing              : 0.20
% 9.78/3.63  CNF conversion       : 0.03
% 9.78/3.63  Main loop            : 2.46
% 9.78/3.63  Inferencing          : 0.82
% 9.78/3.63  Reduction            : 0.91
% 9.78/3.63  Demodulation         : 0.66
% 9.78/3.63  BG Simplification    : 0.09
% 9.78/3.63  Subsumption          : 0.49
% 9.78/3.63  Abstraction          : 0.13
% 9.78/3.63  MUC search           : 0.00
% 9.78/3.63  Cooper               : 0.00
% 9.78/3.63  Total                : 2.90
% 9.78/3.63  Index Insertion      : 0.00
% 9.78/3.63  Index Deletion       : 0.00
% 9.78/3.63  Index Matching       : 0.00
% 9.78/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
