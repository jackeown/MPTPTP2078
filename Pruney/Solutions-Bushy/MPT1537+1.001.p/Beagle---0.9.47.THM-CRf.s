%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1537+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:01 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  606 (8616 expanded)
%              Number of leaves         :   22 (2584 expanded)
%              Depth                    :   28
%              Number of atoms          : 2302 (45290 expanded)
%              Number of equality atoms :   71 (1145 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_9 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( r1_yellow_0(A,B)
          <=> ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r2_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r2_lattice3(A,B,E)
                           => r1_orders_2(A,D,E) ) ) )
                   => D = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r1_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    r1_yellow_0('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1,B_39] :
      ( r2_lattice3(A_1,B_39,'#skF_3'(A_1,B_39))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_39] :
      ( m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_7')
      | r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_68,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_6')
    | r1_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_75,plain,(
    ~ r1_yellow_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_22,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r1_orders_2(A_1,'#skF_2'(A_1,B_39,C_58),E_64)
      | ~ r2_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1301,plain,(
    ! [A_279,B_280,C_281,E_282] :
      ( m1_subset_1('#skF_1'(A_279,B_280,C_281),u1_struct_0(A_279))
      | r1_orders_2(A_279,'#skF_2'(A_279,B_280,C_281),E_282)
      | ~ r2_lattice3(A_279,B_280,E_282)
      | ~ m1_subset_1(E_282,u1_struct_0(A_279))
      | r1_yellow_0(A_279,B_280)
      | ~ r2_lattice3(A_279,B_280,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_334,plain,(
    ! [A_182,B_183,C_184,E_185] :
      ( m1_subset_1('#skF_1'(A_182,B_183,C_184),u1_struct_0(A_182))
      | r1_orders_2(A_182,'#skF_2'(A_182,B_183,C_184),E_185)
      | ~ r2_lattice3(A_182,B_183,E_185)
      | ~ m1_subset_1(E_185,u1_struct_0(A_182))
      | r1_yellow_0(A_182,B_183)
      | ~ r2_lattice3(A_182,B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ l1_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    ! [D_96,C_100] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_109,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_89,plain,(
    ! [A_107,B_108,D_109] :
      ( r1_orders_2(A_107,'#skF_3'(A_107,B_108),D_109)
      | ~ r2_lattice3(A_107,B_108,D_109)
      | ~ m1_subset_1(D_109,u1_struct_0(A_107))
      | ~ r1_yellow_0(A_107,B_108)
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_93,plain,(
    ! [B_108] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_108))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_108),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_108,'#skF_9'('#skF_3'('#skF_5',B_108)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_108)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_108)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_89,c_83])).

tff(c_124,plain,(
    ! [B_142] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_142))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_142),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_142,'#skF_9'('#skF_3'('#skF_5',B_142)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_142)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_93])).

tff(c_127,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_109,c_124])).

tff(c_130,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_134])).

tff(c_140,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_62,plain,(
    ! [D_96,C_100] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_139,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_141,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_144,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_110,c_141])).

tff(c_147,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_144])).

tff(c_155,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_155])).

tff(c_160,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_164,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_164])).

tff(c_169,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_338,plain,(
    ! [B_183,C_184,E_185] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_183,C_184))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_183,C_184))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_183,C_184),E_185)
      | ~ r2_lattice3('#skF_5',B_183,E_185)
      | ~ m1_subset_1(E_185,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_183)
      | ~ r2_lattice3('#skF_5',B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_334,c_169])).

tff(c_708,plain,(
    ! [B_213,C_214,E_215] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_213,C_214))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_213,C_214))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_213,C_214),E_215)
      | ~ r2_lattice3('#skF_5',B_213,E_215)
      | ~ m1_subset_1(E_215,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_213)
      | ~ r2_lattice3('#skF_5',B_213,C_214)
      | ~ m1_subset_1(C_214,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_338])).

tff(c_711,plain,(
    ! [C_58,E_215,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_215)
      | ~ r2_lattice3('#skF_5','#skF_6',E_215)
      | ~ m1_subset_1(E_215,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_708])).

tff(c_721,plain,(
    ! [C_58,E_215,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_215)
      | ~ r2_lattice3('#skF_5','#skF_6',E_215)
      | ~ m1_subset_1(E_215,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_711])).

tff(c_774,plain,(
    ! [C_225,E_226,E_227] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_225))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_225),E_226)
      | ~ r2_lattice3('#skF_5','#skF_6',E_226)
      | ~ m1_subset_1(E_226,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_225),E_227)
      | ~ r2_lattice3('#skF_5','#skF_6',E_227)
      | ~ m1_subset_1(E_227,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_225)
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_721])).

tff(c_16,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1('#skF_1'(A_155,B_156,C_157),u1_struct_0(A_155))
      | '#skF_2'(A_155,B_156,C_157) != C_157
      | r1_yellow_0(A_155,B_156)
      | ~ r2_lattice3(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [B_156,C_157] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_156,C_157))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_156,C_157))
      | '#skF_2'('#skF_5',B_156,C_157) != C_157
      | r1_yellow_0('#skF_5',B_156)
      | ~ r2_lattice3('#skF_5',B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_213,c_169])).

tff(c_287,plain,(
    ! [B_179,C_180] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_179,C_180))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_179,C_180))
      | '#skF_2'('#skF_5',B_179,C_180) != C_180
      | r1_yellow_0('#skF_5',B_179)
      | ~ r2_lattice3('#skF_5',B_179,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_217])).

tff(c_297,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_287])).

tff(c_304,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_297])).

tff(c_306,plain,(
    ! [C_181] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_181))
      | '#skF_2'('#skF_5','#skF_6',C_181) != C_181
      | ~ r2_lattice3('#skF_5','#skF_6',C_181)
      | ~ m1_subset_1(C_181,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_304])).

tff(c_14,plain,(
    ! [A_1,C_58,B_39] :
      ( ~ r1_orders_2(A_1,C_58,'#skF_1'(A_1,B_39,C_58))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_316,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_306,c_14])).

tff(c_329,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_316])).

tff(c_330,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_329])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r2_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_263,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_subset_1('#skF_1'(A_171,B_172,C_173),u1_struct_0(A_171))
      | r2_lattice3(A_171,B_172,'#skF_2'(A_171,B_172,C_173))
      | r1_yellow_0(A_171,B_172)
      | ~ r2_lattice3(A_171,B_172,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_267,plain,(
    ! [B_172,C_173] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_172,C_173))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_172,C_173))
      | r2_lattice3('#skF_5',B_172,'#skF_2'('#skF_5',B_172,C_173))
      | r1_yellow_0('#skF_5',B_172)
      | ~ r2_lattice3('#skF_5',B_172,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_263,c_169])).

tff(c_384,plain,(
    ! [B_191,C_192] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_191,C_192))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_191,C_192))
      | r2_lattice3('#skF_5',B_191,'#skF_2'('#skF_5',B_191,C_192))
      | r1_yellow_0('#skF_5',B_191)
      | ~ r2_lattice3('#skF_5',B_191,C_192)
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_267])).

tff(c_387,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_384])).

tff(c_394,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_387])).

tff(c_395,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_394])).

tff(c_221,plain,(
    ! [A_158,B_159,C_160] :
      ( r2_lattice3(A_158,B_159,'#skF_1'(A_158,B_159,C_160))
      | m1_subset_1('#skF_2'(A_158,B_159,C_160),u1_struct_0(A_158))
      | r1_yellow_0(A_158,B_159)
      | ~ r2_lattice3(A_158,B_159,C_160)
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_225,plain,(
    ! [B_159,C_160] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_159,C_160))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_159,C_160))
      | r2_lattice3('#skF_5',B_159,'#skF_1'('#skF_5',B_159,C_160))
      | r1_yellow_0('#skF_5',B_159)
      | ~ r2_lattice3('#skF_5',B_159,C_160)
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_221,c_169])).

tff(c_401,plain,(
    ! [B_194,C_195] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_194,C_195))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_194,C_195))
      | r2_lattice3('#skF_5',B_194,'#skF_1'('#skF_5',B_194,C_195))
      | r1_yellow_0('#skF_5',B_194)
      | ~ r2_lattice3('#skF_5',B_194,C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_225])).

tff(c_403,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_395,c_401])).

tff(c_407,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_403])).

tff(c_279,plain,(
    ! [A_176,B_177,C_178] :
      ( m1_subset_1('#skF_1'(A_176,B_177,C_178),u1_struct_0(A_176))
      | m1_subset_1('#skF_2'(A_176,B_177,C_178),u1_struct_0(A_176))
      | r1_yellow_0(A_176,B_177)
      | ~ r2_lattice3(A_176,B_177,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_283,plain,(
    ! [B_177,C_178] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_177,C_178))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_177,C_178))
      | m1_subset_1('#skF_2'('#skF_5',B_177,C_178),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_177)
      | ~ r2_lattice3('#skF_5',B_177,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_279,c_169])).

tff(c_379,plain,(
    ! [B_189,C_190] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_189,C_190))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_189,C_190))
      | m1_subset_1('#skF_2'('#skF_5',B_189,C_190),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_189)
      | ~ r2_lattice3('#skF_5',B_189,C_190)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_283])).

tff(c_468,plain,(
    ! [B_203,C_204] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_203,C_204))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_203,C_204))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_203,C_204))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_203,C_204))
      | r1_yellow_0('#skF_5',B_203)
      | ~ r2_lattice3('#skF_5',B_203,C_204)
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_379,c_169])).

tff(c_471,plain,(
    ! [C_58] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_407,c_468])).

tff(c_493,plain,(
    ! [C_205] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_205))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_205))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_205))
      | ~ r2_lattice3('#skF_5','#skF_6',C_205)
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_471])).

tff(c_500,plain,(
    ! [C_206] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_206))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_206))
      | ~ r2_lattice3('#skF_5','#skF_6',C_206)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_395,c_493])).

tff(c_32,plain,(
    ! [A_1,C_58,B_39] :
      ( ~ r1_orders_2(A_1,C_58,'#skF_1'(A_1,B_39,C_58))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_506,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_500,c_32])).

tff(c_522,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_506])).

tff(c_523,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_522])).

tff(c_535,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_38,plain,(
    ! [C_78,B_76,A_72] :
      ( C_78 = B_76
      | ~ r1_orders_2(A_72,C_78,B_76)
      | ~ r1_orders_2(A_72,B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_72))
      | ~ m1_subset_1(B_76,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_537,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_535,c_38])).

tff(c_540,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_537])).

tff(c_541,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_540])).

tff(c_603,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_34,plain,(
    ! [A_1,B_39,C_58] :
      ( r2_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_609,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_603])).

tff(c_616,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_609])).

tff(c_617,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_616])).

tff(c_286,plain,(
    ! [B_177,C_178] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_177,C_178))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_177,C_178))
      | m1_subset_1('#skF_2'('#skF_5',B_177,C_178),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_177)
      | ~ r2_lattice3('#skF_5',B_177,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_283])).

tff(c_606,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_286,c_603])).

tff(c_612,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_606])).

tff(c_613,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_612])).

tff(c_639,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_613])).

tff(c_643,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_639,c_32])).

tff(c_657,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_643])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_603,c_657])).

tff(c_660,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_777,plain,(
    ! [E_227] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_227)
      | ~ r2_lattice3('#skF_5','#skF_6',E_227)
      | ~ m1_subset_1(E_227,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_774,c_660])).

tff(c_835,plain,(
    ! [E_227] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_227)
      | ~ r2_lattice3('#skF_5','#skF_6',E_227)
      | ~ m1_subset_1(E_227,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_777])).

tff(c_900,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_20,plain,(
    ! [A_1,C_58,B_39,E_64] :
      ( ~ r1_orders_2(A_1,C_58,'#skF_1'(A_1,B_39,C_58))
      | r1_orders_2(A_1,'#skF_2'(A_1,B_39,C_58),E_64)
      | ~ r2_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_902,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_900,c_20])).

tff(c_914,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_902])).

tff(c_937,plain,(
    ! [E_231] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_231)
      | ~ r2_lattice3('#skF_5','#skF_6',E_231)
      | ~ m1_subset_1(E_231,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_914])).

tff(c_940,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_937,c_660])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_940])).

tff(c_985,plain,(
    ! [E_232] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_232)
      | ~ r2_lattice3('#skF_5','#skF_6',E_232)
      | ~ m1_subset_1(E_232,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_988,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_985,c_660])).

tff(c_1018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_988])).

tff(c_1020,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_26,plain,(
    ! [A_1,C_58,B_39] :
      ( ~ r1_orders_2(A_1,C_58,'#skF_1'(A_1,B_39,C_58))
      | r2_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_509,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_500,c_26])).

tff(c_526,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_509])).

tff(c_527,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_526])).

tff(c_1025,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_527])).

tff(c_1019,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_1024,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1019,c_169])).

tff(c_1143,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_1024])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_1143])).

tff(c_1145,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1305,plain,(
    ! [B_280,C_281,E_282] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_280,C_281))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_280,C_281))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_280,C_281),E_282)
      | ~ r2_lattice3('#skF_5',B_280,E_282)
      | ~ m1_subset_1(E_282,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_280)
      | ~ r2_lattice3('#skF_5',B_280,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1301,c_1145])).

tff(c_1729,plain,(
    ! [B_311,C_312,E_313] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_311,C_312))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_311,C_312))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_311,C_312),E_313)
      | ~ r2_lattice3('#skF_5',B_311,E_313)
      | ~ m1_subset_1(E_313,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_311)
      | ~ r2_lattice3('#skF_5',B_311,C_312)
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1305])).

tff(c_1734,plain,(
    ! [C_58,E_313,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_313)
      | ~ r2_lattice3('#skF_5','#skF_6',E_313)
      | ~ m1_subset_1(E_313,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1729])).

tff(c_1746,plain,(
    ! [C_58,E_313,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_313)
      | ~ r2_lattice3('#skF_5','#skF_6',E_313)
      | ~ m1_subset_1(E_313,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1734])).

tff(c_1782,plain,(
    ! [C_321,E_322,E_323] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_321))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_321),E_322)
      | ~ r2_lattice3('#skF_5','#skF_6',E_322)
      | ~ m1_subset_1(E_322,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_321),E_323)
      | ~ r2_lattice3('#skF_5','#skF_6',E_323)
      | ~ m1_subset_1(E_323,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_321)
      | ~ m1_subset_1(C_321,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1746])).

tff(c_1194,plain,(
    ! [A_244,B_245,C_246] :
      ( m1_subset_1('#skF_1'(A_244,B_245,C_246),u1_struct_0(A_244))
      | '#skF_2'(A_244,B_245,C_246) != C_246
      | r1_yellow_0(A_244,B_245)
      | ~ r2_lattice3(A_244,B_245,C_246)
      | ~ m1_subset_1(C_246,u1_struct_0(A_244))
      | ~ l1_orders_2(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1198,plain,(
    ! [B_245,C_246] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_245,C_246))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_245,C_246))
      | '#skF_2'('#skF_5',B_245,C_246) != C_246
      | r1_yellow_0('#skF_5',B_245)
      | ~ r2_lattice3('#skF_5',B_245,C_246)
      | ~ m1_subset_1(C_246,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1194,c_1145])).

tff(c_1247,plain,(
    ! [B_271,C_272] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_271,C_272))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_271,C_272))
      | '#skF_2'('#skF_5',B_271,C_272) != C_272
      | r1_yellow_0('#skF_5',B_271)
      | ~ r2_lattice3('#skF_5',B_271,C_272)
      | ~ m1_subset_1(C_272,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1198])).

tff(c_1257,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_1247])).

tff(c_1264,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1257])).

tff(c_1266,plain,(
    ! [C_273] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_273))
      | '#skF_2'('#skF_5','#skF_6',C_273) != C_273
      | ~ r2_lattice3('#skF_5','#skF_6',C_273)
      | ~ m1_subset_1(C_273,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1264])).

tff(c_1276,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1266,c_14])).

tff(c_1289,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_1276])).

tff(c_1290,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1289])).

tff(c_1226,plain,(
    ! [A_263,B_264,C_265] :
      ( m1_subset_1('#skF_1'(A_263,B_264,C_265),u1_struct_0(A_263))
      | r2_lattice3(A_263,B_264,'#skF_2'(A_263,B_264,C_265))
      | r1_yellow_0(A_263,B_264)
      | ~ r2_lattice3(A_263,B_264,C_265)
      | ~ m1_subset_1(C_265,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1230,plain,(
    ! [B_264,C_265] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_264,C_265))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_264,C_265))
      | r2_lattice3('#skF_5',B_264,'#skF_2'('#skF_5',B_264,C_265))
      | r1_yellow_0('#skF_5',B_264)
      | ~ r2_lattice3('#skF_5',B_264,C_265)
      | ~ m1_subset_1(C_265,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1226,c_1145])).

tff(c_1341,plain,(
    ! [B_283,C_284] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_283,C_284))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_283,C_284))
      | r2_lattice3('#skF_5',B_283,'#skF_2'('#skF_5',B_283,C_284))
      | r1_yellow_0('#skF_5',B_283)
      | ~ r2_lattice3('#skF_5',B_283,C_284)
      | ~ m1_subset_1(C_284,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1230])).

tff(c_1344,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_1341])).

tff(c_1351,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1344])).

tff(c_1352,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1351])).

tff(c_1357,plain,(
    ! [C_285] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_285))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_285))
      | ~ r2_lattice3('#skF_5','#skF_6',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1351])).

tff(c_1212,plain,(
    ! [A_254,B_255,C_256] :
      ( r2_lattice3(A_254,B_255,'#skF_1'(A_254,B_255,C_256))
      | m1_subset_1('#skF_2'(A_254,B_255,C_256),u1_struct_0(A_254))
      | r1_yellow_0(A_254,B_255)
      | ~ r2_lattice3(A_254,B_255,C_256)
      | ~ m1_subset_1(C_256,u1_struct_0(A_254))
      | ~ l1_orders_2(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1216,plain,(
    ! [B_255,C_256] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_255,C_256))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_255,C_256))
      | r2_lattice3('#skF_5',B_255,'#skF_1'('#skF_5',B_255,C_256))
      | r1_yellow_0('#skF_5',B_255)
      | ~ r2_lattice3('#skF_5',B_255,C_256)
      | ~ m1_subset_1(C_256,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1212,c_1145])).

tff(c_1219,plain,(
    ! [B_255,C_256] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_255,C_256))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_255,C_256))
      | r2_lattice3('#skF_5',B_255,'#skF_1'('#skF_5',B_255,C_256))
      | r1_yellow_0('#skF_5',B_255)
      | ~ r2_lattice3('#skF_5',B_255,C_256)
      | ~ m1_subset_1(C_256,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1216])).

tff(c_1359,plain,(
    ! [C_285] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_285))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_285))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_285))
      | ~ r2_lattice3('#skF_5','#skF_6',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1357,c_1219])).

tff(c_1362,plain,(
    ! [C_285] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_285))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_285))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_285))
      | ~ r2_lattice3('#skF_5','#skF_6',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1359])).

tff(c_1204,plain,(
    ! [A_251,B_252,C_253] :
      ( m1_subset_1('#skF_1'(A_251,B_252,C_253),u1_struct_0(A_251))
      | m1_subset_1('#skF_2'(A_251,B_252,C_253),u1_struct_0(A_251))
      | r1_yellow_0(A_251,B_252)
      | ~ r2_lattice3(A_251,B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0(A_251))
      | ~ l1_orders_2(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1208,plain,(
    ! [B_252,C_253] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_252,C_253))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_252,C_253))
      | m1_subset_1('#skF_2'('#skF_5',B_252,C_253),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_252)
      | ~ r2_lattice3('#skF_5',B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1204,c_1145])).

tff(c_1373,plain,(
    ! [B_287,C_288] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_287,C_288))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_287,C_288))
      | m1_subset_1('#skF_2'('#skF_5',B_287,C_288),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_287)
      | ~ r2_lattice3('#skF_5',B_287,C_288)
      | ~ m1_subset_1(C_288,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1208])).

tff(c_1480,plain,(
    ! [B_299,C_300] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_299,C_300))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_299,C_300))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_299,C_300))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_299,C_300))
      | r1_yellow_0('#skF_5',B_299)
      | ~ r2_lattice3('#skF_5',B_299,C_300)
      | ~ m1_subset_1(C_300,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1373,c_1145])).

tff(c_1487,plain,(
    ! [C_285] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_285))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_285))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_285))
      | ~ r2_lattice3('#skF_5','#skF_6',C_285)
      | ~ m1_subset_1(C_285,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1362,c_1480])).

tff(c_1513,plain,(
    ! [C_301] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_301))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_301))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_301))
      | ~ r2_lattice3('#skF_5','#skF_6',C_301)
      | ~ m1_subset_1(C_301,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1487])).

tff(c_1520,plain,(
    ! [C_302] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_302))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_302))
      | ~ r2_lattice3('#skF_5','#skF_6',C_302)
      | ~ m1_subset_1(C_302,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1352,c_1513])).

tff(c_1526,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1520,c_32])).

tff(c_1542,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_1526])).

tff(c_1543,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1542])).

tff(c_1555,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1543])).

tff(c_1557,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1555,c_38])).

tff(c_1560,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_1557])).

tff(c_1561,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_1560])).

tff(c_1563,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1561])).

tff(c_1569,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1563])).

tff(c_1576,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_1569])).

tff(c_1577,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1576])).

tff(c_1211,plain,(
    ! [B_252,C_253] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_252,C_253))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_252,C_253))
      | m1_subset_1('#skF_2'('#skF_5',B_252,C_253),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_252)
      | ~ r2_lattice3('#skF_5',B_252,C_253)
      | ~ m1_subset_1(C_253,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1208])).

tff(c_1566,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1211,c_1563])).

tff(c_1572,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_1566])).

tff(c_1573,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1572])).

tff(c_1628,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1577,c_1573])).

tff(c_1632,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_1628,c_32])).

tff(c_1646,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_1632])).

tff(c_1648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1563,c_1646])).

tff(c_1649,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1561])).

tff(c_1785,plain,(
    ! [E_323] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_323)
      | ~ r2_lattice3('#skF_5','#skF_6',E_323)
      | ~ m1_subset_1(E_323,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1782,c_1649])).

tff(c_1843,plain,(
    ! [E_323] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_323)
      | ~ r2_lattice3('#skF_5','#skF_6',E_323)
      | ~ m1_subset_1(E_323,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_1785])).

tff(c_1891,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1843])).

tff(c_1893,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1891,c_20])).

tff(c_1905,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_1893])).

tff(c_1945,plain,(
    ! [E_327] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_327)
      | ~ r2_lattice3('#skF_5','#skF_6',E_327)
      | ~ m1_subset_1(E_327,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1905])).

tff(c_1948,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1945,c_1649])).

tff(c_1978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_1948])).

tff(c_1998,plain,(
    ! [E_330] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_330)
      | ~ r2_lattice3('#skF_5','#skF_6',E_330)
      | ~ m1_subset_1(E_330,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1843])).

tff(c_2001,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1998,c_1649])).

tff(c_2031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_2001])).

tff(c_2033,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1543])).

tff(c_1529,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1520,c_26])).

tff(c_1546,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_40,c_1529])).

tff(c_1547,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1546])).

tff(c_2038,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_2033,c_1547])).

tff(c_2032,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1543])).

tff(c_2037,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2032,c_1145])).

tff(c_2125,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_2037])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2033,c_2125])).

tff(c_2127,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2133,plain,(
    ! [A_336,B_337,D_338] :
      ( r1_orders_2(A_336,'#skF_3'(A_336,B_337),D_338)
      | ~ r2_lattice3(A_336,B_337,D_338)
      | ~ m1_subset_1(D_338,u1_struct_0(A_336))
      | ~ r1_yellow_0(A_336,B_337)
      | ~ l1_orders_2(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2137,plain,(
    ! [B_337] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_337))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_337),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_337,'#skF_9'('#skF_3'('#skF_5',B_337)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_337)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_337)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2133,c_83])).

tff(c_2175,plain,(
    ! [B_378] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_378))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_378),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_378,'#skF_9'('#skF_3'('#skF_5',B_378)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_378)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2137])).

tff(c_2178,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2127,c_2175])).

tff(c_2181,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2178])).

tff(c_2182,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2181])).

tff(c_2185,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2182])).

tff(c_2189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2185])).

tff(c_2191,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2181])).

tff(c_2128,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_64,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_6','#skF_7')
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2129,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2128,c_64])).

tff(c_2190,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2181])).

tff(c_2192,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2190])).

tff(c_2195,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2129,c_2192])).

tff(c_2198,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2191,c_2195])).

tff(c_2230,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2198])).

tff(c_2234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2230])).

tff(c_2235,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2190])).

tff(c_2239,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2235])).

tff(c_2243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2239])).

tff(c_2244,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4425,plain,(
    ! [A_646,B_647,C_648,E_649] :
      ( m1_subset_1('#skF_1'(A_646,B_647,C_648),u1_struct_0(A_646))
      | r1_orders_2(A_646,'#skF_2'(A_646,B_647,C_648),E_649)
      | ~ r2_lattice3(A_646,B_647,E_649)
      | ~ m1_subset_1(E_649,u1_struct_0(A_646))
      | r1_yellow_0(A_646,B_647)
      | ~ r2_lattice3(A_646,B_647,C_648)
      | ~ m1_subset_1(C_648,u1_struct_0(A_646))
      | ~ l1_orders_2(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3447,plain,(
    ! [A_543,B_544,C_545,E_546] :
      ( m1_subset_1('#skF_1'(A_543,B_544,C_545),u1_struct_0(A_543))
      | r1_orders_2(A_543,'#skF_2'(A_543,B_544,C_545),E_546)
      | ~ r2_lattice3(A_543,B_544,E_546)
      | ~ m1_subset_1(E_546,u1_struct_0(A_543))
      | r1_yellow_0(A_543,B_544)
      | ~ r2_lattice3(A_543,B_544,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0(A_543))
      | ~ l1_orders_2(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2441,plain,(
    ! [A_447,B_448,C_449,E_450] :
      ( m1_subset_1('#skF_1'(A_447,B_448,C_449),u1_struct_0(A_447))
      | r1_orders_2(A_447,'#skF_2'(A_447,B_448,C_449),E_450)
      | ~ r2_lattice3(A_447,B_448,E_450)
      | ~ m1_subset_1(E_450,u1_struct_0(A_447))
      | r1_yellow_0(A_447,B_448)
      | ~ r2_lattice3(A_447,B_448,C_449)
      | ~ m1_subset_1(C_449,u1_struct_0(A_447))
      | ~ l1_orders_2(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2262,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1,B_39,D_69] :
      ( r1_orders_2(A_1,'#skF_3'(A_1,B_39),D_69)
      | ~ r2_lattice3(A_1,B_39,D_69)
      | ~ m1_subset_1(D_69,u1_struct_0(A_1))
      | ~ r1_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [D_96,C_100] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2265,plain,(
    ! [C_402] :
      ( ~ r1_orders_2('#skF_5',C_402,'#skF_9'(C_402))
      | ~ r2_lattice3('#skF_5','#skF_8',C_402)
      | ~ m1_subset_1(C_402,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2269,plain,(
    ! [B_39] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_39))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_39),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_39,'#skF_9'('#skF_3'('#skF_5',B_39)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_39)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_2265])).

tff(c_2289,plain,(
    ! [B_419] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_419))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_419),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_419,'#skF_9'('#skF_3'('#skF_5',B_419)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_419)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2269])).

tff(c_2292,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2262,c_2289])).

tff(c_2295,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2292])).

tff(c_2296,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2295])).

tff(c_2299,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2296])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2299])).

tff(c_2305,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2295])).

tff(c_2274,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2304,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2295])).

tff(c_2306,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2304])).

tff(c_2309,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2274,c_2306])).

tff(c_2312,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2305,c_2309])).

tff(c_2320,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2312])).

tff(c_2324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2320])).

tff(c_2325,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2304])).

tff(c_2329,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2325])).

tff(c_2333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2329])).

tff(c_2334,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2445,plain,(
    ! [B_448,C_449,E_450] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_448,C_449))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_448,C_449))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_448,C_449),E_450)
      | ~ r2_lattice3('#skF_5',B_448,E_450)
      | ~ m1_subset_1(E_450,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_448)
      | ~ r2_lattice3('#skF_5',B_448,C_449)
      | ~ m1_subset_1(C_449,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2441,c_2334])).

tff(c_2917,plain,(
    ! [B_489,C_490,E_491] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_489,C_490))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_489,C_490))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_489,C_490),E_491)
      | ~ r2_lattice3('#skF_5',B_489,E_491)
      | ~ m1_subset_1(E_491,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_489)
      | ~ r2_lattice3('#skF_5',B_489,C_490)
      | ~ m1_subset_1(C_490,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2445])).

tff(c_2920,plain,(
    ! [C_58,E_491,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_491)
      | ~ r2_lattice3('#skF_5','#skF_6',E_491)
      | ~ m1_subset_1(E_491,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_2917])).

tff(c_2930,plain,(
    ! [C_58,E_491,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_491)
      | ~ r2_lattice3('#skF_5','#skF_6',E_491)
      | ~ m1_subset_1(E_491,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2920])).

tff(c_2965,plain,(
    ! [C_498,E_499,E_500] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_498))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_498),E_499)
      | ~ r2_lattice3('#skF_5','#skF_6',E_499)
      | ~ m1_subset_1(E_499,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_498),E_500)
      | ~ r2_lattice3('#skF_5','#skF_6',E_500)
      | ~ m1_subset_1(E_500,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_498)
      | ~ m1_subset_1(C_498,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2930])).

tff(c_18,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r1_yellow_0(A_1,B_39)
      | ~ r2_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2335,plain,(
    ! [D_423] :
      ( r1_orders_2('#skF_5','#skF_7',D_423)
      | ~ r2_lattice3('#skF_5','#skF_6',D_423)
      | ~ m1_subset_1(D_423,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2339,plain,(
    ! [B_39,C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_39,C_58))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_39,C_58))
      | '#skF_2'('#skF_5',B_39,C_58) != C_58
      | r1_yellow_0('#skF_5',B_39)
      | ~ r2_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_2335])).

tff(c_2485,plain,(
    ! [B_453,C_454] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_453,C_454))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_453,C_454))
      | '#skF_2'('#skF_5',B_453,C_454) != C_454
      | r1_yellow_0('#skF_5',B_453)
      | ~ r2_lattice3('#skF_5',B_453,C_454)
      | ~ m1_subset_1(C_454,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2339])).

tff(c_2495,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_2485])).

tff(c_2502,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2495])).

tff(c_2504,plain,(
    ! [C_455] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_455))
      | '#skF_2'('#skF_5','#skF_6',C_455) != C_455
      | ~ r2_lattice3('#skF_5','#skF_6',C_455)
      | ~ m1_subset_1(C_455,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2502])).

tff(c_2514,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2504,c_14])).

tff(c_2527,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_2514])).

tff(c_2528,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2527])).

tff(c_2401,plain,(
    ! [A_437,B_438,C_439] :
      ( m1_subset_1('#skF_1'(A_437,B_438,C_439),u1_struct_0(A_437))
      | r2_lattice3(A_437,B_438,'#skF_2'(A_437,B_438,C_439))
      | r1_yellow_0(A_437,B_438)
      | ~ r2_lattice3(A_437,B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0(A_437))
      | ~ l1_orders_2(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2405,plain,(
    ! [B_438,C_439] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_438,C_439))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_438,C_439))
      | r2_lattice3('#skF_5',B_438,'#skF_2'('#skF_5',B_438,C_439))
      | r1_yellow_0('#skF_5',B_438)
      | ~ r2_lattice3('#skF_5',B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2401,c_2334])).

tff(c_2559,plain,(
    ! [B_465,C_466] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_465,C_466))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_465,C_466))
      | r2_lattice3('#skF_5',B_465,'#skF_2'('#skF_5',B_465,C_466))
      | r1_yellow_0('#skF_5',B_465)
      | ~ r2_lattice3('#skF_5',B_465,C_466)
      | ~ m1_subset_1(C_466,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2405])).

tff(c_2562,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_2559])).

tff(c_2569,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2562])).

tff(c_2570,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2569])).

tff(c_2575,plain,(
    ! [C_467] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_467))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_467))
      | ~ r2_lattice3('#skF_5','#skF_6',C_467)
      | ~ m1_subset_1(C_467,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2569])).

tff(c_2388,plain,(
    ! [A_431,B_432,C_433] :
      ( r2_lattice3(A_431,B_432,'#skF_1'(A_431,B_432,C_433))
      | m1_subset_1('#skF_2'(A_431,B_432,C_433),u1_struct_0(A_431))
      | r1_yellow_0(A_431,B_432)
      | ~ r2_lattice3(A_431,B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0(A_431))
      | ~ l1_orders_2(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2392,plain,(
    ! [B_432,C_433] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_432,C_433))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_432,C_433))
      | r2_lattice3('#skF_5',B_432,'#skF_1'('#skF_5',B_432,C_433))
      | r1_yellow_0('#skF_5',B_432)
      | ~ r2_lattice3('#skF_5',B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2388,c_2334])).

tff(c_2395,plain,(
    ! [B_432,C_433] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_432,C_433))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_432,C_433))
      | r2_lattice3('#skF_5',B_432,'#skF_1'('#skF_5',B_432,C_433))
      | r1_yellow_0('#skF_5',B_432)
      | ~ r2_lattice3('#skF_5',B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2392])).

tff(c_2577,plain,(
    ! [C_467] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_467))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_467))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_467))
      | ~ r2_lattice3('#skF_5','#skF_6',C_467)
      | ~ m1_subset_1(C_467,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2575,c_2395])).

tff(c_2580,plain,(
    ! [C_467] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_467))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_467))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_467))
      | ~ r2_lattice3('#skF_5','#skF_6',C_467)
      | ~ m1_subset_1(C_467,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2577])).

tff(c_2410,plain,(
    ! [A_443,B_444,C_445] :
      ( m1_subset_1('#skF_1'(A_443,B_444,C_445),u1_struct_0(A_443))
      | m1_subset_1('#skF_2'(A_443,B_444,C_445),u1_struct_0(A_443))
      | r1_yellow_0(A_443,B_444)
      | ~ r2_lattice3(A_443,B_444,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0(A_443))
      | ~ l1_orders_2(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2414,plain,(
    ! [B_444,C_445] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_444,C_445))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_444,C_445))
      | m1_subset_1('#skF_2'('#skF_5',B_444,C_445),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_444)
      | ~ r2_lattice3('#skF_5',B_444,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2410,c_2334])).

tff(c_2591,plain,(
    ! [B_469,C_470] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_469,C_470))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_469,C_470))
      | m1_subset_1('#skF_2'('#skF_5',B_469,C_470),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_469)
      | ~ r2_lattice3('#skF_5',B_469,C_470)
      | ~ m1_subset_1(C_470,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2414])).

tff(c_2682,plain,(
    ! [B_477,C_478] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_477,C_478))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_477,C_478))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_477,C_478))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_477,C_478))
      | r1_yellow_0('#skF_5',B_477)
      | ~ r2_lattice3('#skF_5',B_477,C_478)
      | ~ m1_subset_1(C_478,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2591,c_2334])).

tff(c_2689,plain,(
    ! [C_467] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_467))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_467))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_467))
      | ~ r2_lattice3('#skF_5','#skF_6',C_467)
      | ~ m1_subset_1(C_467,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2580,c_2682])).

tff(c_2715,plain,(
    ! [C_479] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_479))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_479))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_479))
      | ~ r2_lattice3('#skF_5','#skF_6',C_479)
      | ~ m1_subset_1(C_479,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2689])).

tff(c_2722,plain,(
    ! [C_480] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_480))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_480))
      | ~ r2_lattice3('#skF_5','#skF_6',C_480)
      | ~ m1_subset_1(C_480,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2570,c_2715])).

tff(c_2728,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2722,c_32])).

tff(c_2744,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_2728])).

tff(c_2745,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2744])).

tff(c_2757,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2745])).

tff(c_2759,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2757,c_38])).

tff(c_2762,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_2759])).

tff(c_2763,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2528,c_2762])).

tff(c_2765,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2763])).

tff(c_2771,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_2765])).

tff(c_2778,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_2771])).

tff(c_2779,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2778])).

tff(c_2417,plain,(
    ! [B_444,C_445] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_444,C_445))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_444,C_445))
      | m1_subset_1('#skF_2'('#skF_5',B_444,C_445),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_444)
      | ~ r2_lattice3('#skF_5',B_444,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2414])).

tff(c_2768,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2417,c_2765])).

tff(c_2774,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_2768])).

tff(c_2775,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2774])).

tff(c_2830,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2779,c_2775])).

tff(c_2834,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2830,c_32])).

tff(c_2848,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_2834])).

tff(c_2850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2765,c_2848])).

tff(c_2851,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2763])).

tff(c_2968,plain,(
    ! [E_500] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_500)
      | ~ r2_lattice3('#skF_5','#skF_6',E_500)
      | ~ m1_subset_1(E_500,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2965,c_2851])).

tff(c_3026,plain,(
    ! [E_500] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_500)
      | ~ r2_lattice3('#skF_5','#skF_6',E_500)
      | ~ m1_subset_1(E_500,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_2968])).

tff(c_3074,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3026])).

tff(c_3076,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3074,c_20])).

tff(c_3088,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_3076])).

tff(c_3128,plain,(
    ! [E_504] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_504)
      | ~ r2_lattice3('#skF_5','#skF_6',E_504)
      | ~ m1_subset_1(E_504,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3088])).

tff(c_3131,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3128,c_2851])).

tff(c_3161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_3131])).

tff(c_3177,plain,(
    ! [E_507] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_507)
      | ~ r2_lattice3('#skF_5','#skF_6',E_507)
      | ~ m1_subset_1(E_507,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_3026])).

tff(c_3180,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3177,c_2851])).

tff(c_3210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_3180])).

tff(c_3212,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2745])).

tff(c_2731,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2722,c_26])).

tff(c_2748,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_2731])).

tff(c_2749,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2748])).

tff(c_3217,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_3212,c_2749])).

tff(c_3211,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2745])).

tff(c_3216,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3211,c_2334])).

tff(c_3304,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3217,c_3216])).

tff(c_3305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3212,c_3304])).

tff(c_3306,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3451,plain,(
    ! [B_544,C_545,E_546] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_544,C_545))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_544,C_545))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_544,C_545),E_546)
      | ~ r2_lattice3('#skF_5',B_544,E_546)
      | ~ m1_subset_1(E_546,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_544)
      | ~ r2_lattice3('#skF_5',B_544,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3447,c_3306])).

tff(c_3695,plain,(
    ! [B_572,C_573,E_574] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_572,C_573))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_572,C_573))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_572,C_573),E_574)
      | ~ r2_lattice3('#skF_5',B_572,E_574)
      | ~ m1_subset_1(E_574,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_572)
      | ~ r2_lattice3('#skF_5',B_572,C_573)
      | ~ m1_subset_1(C_573,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3451])).

tff(c_3698,plain,(
    ! [C_58,E_574,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_574)
      | ~ r2_lattice3('#skF_5','#skF_6',E_574)
      | ~ m1_subset_1(E_574,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_3695])).

tff(c_3708,plain,(
    ! [C_58,E_574,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_574)
      | ~ r2_lattice3('#skF_5','#skF_6',E_574)
      | ~ m1_subset_1(E_574,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3698])).

tff(c_3709,plain,(
    ! [C_58,E_574,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_574)
      | ~ r2_lattice3('#skF_5','#skF_6',E_574)
      | ~ m1_subset_1(E_574,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3708])).

tff(c_4019,plain,(
    ! [C_593,E_594] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_593))
      | ~ r2_lattice3('#skF_5','#skF_6',E_594)
      | ~ m1_subset_1(E_594,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_593)
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_593),E_594) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3709])).

tff(c_3343,plain,(
    ! [A_514,B_515,C_516] :
      ( m1_subset_1('#skF_1'(A_514,B_515,C_516),u1_struct_0(A_514))
      | '#skF_2'(A_514,B_515,C_516) != C_516
      | r1_yellow_0(A_514,B_515)
      | ~ r2_lattice3(A_514,B_515,C_516)
      | ~ m1_subset_1(C_516,u1_struct_0(A_514))
      | ~ l1_orders_2(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3347,plain,(
    ! [B_515,C_516] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_515,C_516))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_515,C_516))
      | '#skF_2'('#skF_5',B_515,C_516) != C_516
      | r1_yellow_0('#skF_5',B_515)
      | ~ r2_lattice3('#skF_5',B_515,C_516)
      | ~ m1_subset_1(C_516,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3343,c_3306])).

tff(c_3400,plain,(
    ! [B_540,C_541] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_540,C_541))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_540,C_541))
      | '#skF_2'('#skF_5',B_540,C_541) != C_541
      | r1_yellow_0('#skF_5',B_540)
      | ~ r2_lattice3('#skF_5',B_540,C_541)
      | ~ m1_subset_1(C_541,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3347])).

tff(c_3410,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_3400])).

tff(c_3417,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3410])).

tff(c_3419,plain,(
    ! [C_542] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_542))
      | '#skF_2'('#skF_5','#skF_6',C_542) != C_542
      | ~ r2_lattice3('#skF_5','#skF_6',C_542)
      | ~ m1_subset_1(C_542,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3417])).

tff(c_3429,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3419,c_14])).

tff(c_3442,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_3429])).

tff(c_3443,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3442])).

tff(c_3392,plain,(
    ! [A_537,B_538,C_539] :
      ( m1_subset_1('#skF_1'(A_537,B_538,C_539),u1_struct_0(A_537))
      | r2_lattice3(A_537,B_538,'#skF_2'(A_537,B_538,C_539))
      | r1_yellow_0(A_537,B_538)
      | ~ r2_lattice3(A_537,B_538,C_539)
      | ~ m1_subset_1(C_539,u1_struct_0(A_537))
      | ~ l1_orders_2(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3396,plain,(
    ! [B_538,C_539] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_538,C_539))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_538,C_539))
      | r2_lattice3('#skF_5',B_538,'#skF_2'('#skF_5',B_538,C_539))
      | r1_yellow_0('#skF_5',B_538)
      | ~ r2_lattice3('#skF_5',B_538,C_539)
      | ~ m1_subset_1(C_539,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3392,c_3306])).

tff(c_3476,plain,(
    ! [B_547,C_548] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_547,C_548))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_547,C_548))
      | r2_lattice3('#skF_5',B_547,'#skF_2'('#skF_5',B_547,C_548))
      | r1_yellow_0('#skF_5',B_547)
      | ~ r2_lattice3('#skF_5',B_547,C_548)
      | ~ m1_subset_1(C_548,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3396])).

tff(c_3479,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_3476])).

tff(c_3486,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3479])).

tff(c_3487,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3486])).

tff(c_3362,plain,(
    ! [A_523,B_524,C_525] :
      ( r2_lattice3(A_523,B_524,'#skF_1'(A_523,B_524,C_525))
      | m1_subset_1('#skF_2'(A_523,B_524,C_525),u1_struct_0(A_523))
      | r1_yellow_0(A_523,B_524)
      | ~ r2_lattice3(A_523,B_524,C_525)
      | ~ m1_subset_1(C_525,u1_struct_0(A_523))
      | ~ l1_orders_2(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3366,plain,(
    ! [B_524,C_525] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_524,C_525))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_524,C_525))
      | r2_lattice3('#skF_5',B_524,'#skF_1'('#skF_5',B_524,C_525))
      | r1_yellow_0('#skF_5',B_524)
      | ~ r2_lattice3('#skF_5',B_524,C_525)
      | ~ m1_subset_1(C_525,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3362,c_3306])).

tff(c_3502,plain,(
    ! [B_553,C_554] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_553,C_554))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_553,C_554))
      | r2_lattice3('#skF_5',B_553,'#skF_1'('#skF_5',B_553,C_554))
      | r1_yellow_0('#skF_5',B_553)
      | ~ r2_lattice3('#skF_5',B_553,C_554)
      | ~ m1_subset_1(C_554,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3366])).

tff(c_3504,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3487,c_3502])).

tff(c_3508,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3504])).

tff(c_3375,plain,(
    ! [A_529,B_530,C_531] :
      ( m1_subset_1('#skF_1'(A_529,B_530,C_531),u1_struct_0(A_529))
      | m1_subset_1('#skF_2'(A_529,B_530,C_531),u1_struct_0(A_529))
      | r1_yellow_0(A_529,B_530)
      | ~ r2_lattice3(A_529,B_530,C_531)
      | ~ m1_subset_1(C_531,u1_struct_0(A_529))
      | ~ l1_orders_2(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3379,plain,(
    ! [B_530,C_531] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_530,C_531))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_530,C_531))
      | m1_subset_1('#skF_2'('#skF_5',B_530,C_531),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_530)
      | ~ r2_lattice3('#skF_5',B_530,C_531)
      | ~ m1_subset_1(C_531,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3375,c_3306])).

tff(c_3519,plain,(
    ! [B_556,C_557] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_556,C_557))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_556,C_557))
      | m1_subset_1('#skF_2'('#skF_5',B_556,C_557),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_556)
      | ~ r2_lattice3('#skF_5',B_556,C_557)
      | ~ m1_subset_1(C_557,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3379])).

tff(c_3619,plain,(
    ! [B_568,C_569] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_568,C_569))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_568,C_569))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_568,C_569))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_568,C_569))
      | r1_yellow_0('#skF_5',B_568)
      | ~ r2_lattice3('#skF_5',B_568,C_569)
      | ~ m1_subset_1(C_569,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3519,c_3306])).

tff(c_3626,plain,(
    ! [C_58] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3508,c_3619])).

tff(c_3652,plain,(
    ! [C_570] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_570))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_570))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_570))
      | ~ r2_lattice3('#skF_5','#skF_6',C_570)
      | ~ m1_subset_1(C_570,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3626])).

tff(c_3659,plain,(
    ! [C_571] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_571))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_571))
      | ~ r2_lattice3('#skF_5','#skF_6',C_571)
      | ~ m1_subset_1(C_571,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3487,c_3652])).

tff(c_3665,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3659,c_26])).

tff(c_3681,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_3665])).

tff(c_3682,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3681])).

tff(c_3694,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3682])).

tff(c_3719,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_3694,c_38])).

tff(c_3722,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_3719])).

tff(c_3723,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3443,c_3722])).

tff(c_3725,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3723])).

tff(c_3732,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_3725])).

tff(c_3739,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_3732])).

tff(c_3740,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3739])).

tff(c_3382,plain,(
    ! [B_530,C_531] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_530,C_531))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_530,C_531))
      | m1_subset_1('#skF_2'('#skF_5',B_530,C_531),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_530)
      | ~ r2_lattice3('#skF_5',B_530,C_531)
      | ~ m1_subset_1(C_531,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3379])).

tff(c_3729,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3382,c_3725])).

tff(c_3735,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_3729])).

tff(c_3736,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3735])).

tff(c_3768,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3740,c_3736])).

tff(c_3774,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_3768,c_32])).

tff(c_3790,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_3774])).

tff(c_3792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3725,c_3790])).

tff(c_3793,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3723])).

tff(c_4022,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4019,c_3793])).

tff(c_4047,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_4022])).

tff(c_4070,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4047,c_20])).

tff(c_4082,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_4070])).

tff(c_4105,plain,(
    ! [E_595] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_595)
      | ~ r2_lattice3('#skF_5','#skF_6',E_595)
      | ~ m1_subset_1(E_595,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4082])).

tff(c_4108,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4105,c_3793])).

tff(c_4134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_4108])).

tff(c_4136,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3682])).

tff(c_4135,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3682])).

tff(c_3668,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3659,c_32])).

tff(c_3685,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_3668])).

tff(c_3686,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3685])).

tff(c_4166,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4136,c_3686])).

tff(c_4169,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4166,c_3306])).

tff(c_4172,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4135,c_4169])).

tff(c_4174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4136,c_4172])).

tff(c_4175,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4433,plain,(
    ! [B_647,C_648,E_649] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_647,C_648))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_647,C_648))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_647,C_648),E_649)
      | ~ r2_lattice3('#skF_5',B_647,E_649)
      | ~ m1_subset_1(E_649,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_647)
      | ~ r2_lattice3('#skF_5',B_647,C_648)
      | ~ m1_subset_1(C_648,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4425,c_4175])).

tff(c_4563,plain,(
    ! [B_659,C_660,E_661] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_659,C_660))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_659,C_660))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_659,C_660),E_661)
      | ~ r2_lattice3('#skF_5',B_659,E_661)
      | ~ m1_subset_1(E_661,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_659)
      | ~ r2_lattice3('#skF_5',B_659,C_660)
      | ~ m1_subset_1(C_660,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4433])).

tff(c_4566,plain,(
    ! [C_58,E_661,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_661)
      | ~ r2_lattice3('#skF_5','#skF_6',E_661)
      | ~ m1_subset_1(E_661,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_4563])).

tff(c_4576,plain,(
    ! [C_58,E_661,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_661)
      | ~ r2_lattice3('#skF_5','#skF_6',E_661)
      | ~ m1_subset_1(E_661,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4566])).

tff(c_4577,plain,(
    ! [C_58,E_661,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_661)
      | ~ r2_lattice3('#skF_5','#skF_6',E_661)
      | ~ m1_subset_1(E_661,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4576])).

tff(c_4864,plain,(
    ! [C_679,E_680] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_679))
      | ~ r2_lattice3('#skF_5','#skF_6',E_680)
      | ~ m1_subset_1(E_680,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_679)
      | ~ m1_subset_1(C_679,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_679),E_680) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4577])).

tff(c_4211,plain,(
    ! [A_601,B_602,C_603] :
      ( m1_subset_1('#skF_1'(A_601,B_602,C_603),u1_struct_0(A_601))
      | '#skF_2'(A_601,B_602,C_603) != C_603
      | r1_yellow_0(A_601,B_602)
      | ~ r2_lattice3(A_601,B_602,C_603)
      | ~ m1_subset_1(C_603,u1_struct_0(A_601))
      | ~ l1_orders_2(A_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4215,plain,(
    ! [B_602,C_603] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_602,C_603))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_602,C_603))
      | '#skF_2'('#skF_5',B_602,C_603) != C_603
      | r1_yellow_0('#skF_5',B_602)
      | ~ r2_lattice3('#skF_5',B_602,C_603)
      | ~ m1_subset_1(C_603,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4211,c_4175])).

tff(c_4268,plain,(
    ! [B_627,C_628] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_627,C_628))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_627,C_628))
      | '#skF_2'('#skF_5',B_627,C_628) != C_628
      | r1_yellow_0('#skF_5',B_627)
      | ~ r2_lattice3('#skF_5',B_627,C_628)
      | ~ m1_subset_1(C_628,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4215])).

tff(c_4278,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_4268])).

tff(c_4285,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4278])).

tff(c_4287,plain,(
    ! [C_629] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_629))
      | '#skF_2'('#skF_5','#skF_6',C_629) != C_629
      | ~ r2_lattice3('#skF_5','#skF_6',C_629)
      | ~ m1_subset_1(C_629,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4285])).

tff(c_4297,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4287,c_14])).

tff(c_4310,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_4297])).

tff(c_4311,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4310])).

tff(c_4234,plain,(
    ! [A_613,B_614,C_615] :
      ( m1_subset_1('#skF_1'(A_613,B_614,C_615),u1_struct_0(A_613))
      | r2_lattice3(A_613,B_614,'#skF_2'(A_613,B_614,C_615))
      | r1_yellow_0(A_613,B_614)
      | ~ r2_lattice3(A_613,B_614,C_615)
      | ~ m1_subset_1(C_615,u1_struct_0(A_613))
      | ~ l1_orders_2(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4238,plain,(
    ! [B_614,C_615] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_614,C_615))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_614,C_615))
      | r2_lattice3('#skF_5',B_614,'#skF_2'('#skF_5',B_614,C_615))
      | r1_yellow_0('#skF_5',B_614)
      | ~ r2_lattice3('#skF_5',B_614,C_615)
      | ~ m1_subset_1(C_615,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4234,c_4175])).

tff(c_4359,plain,(
    ! [B_639,C_640] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_639,C_640))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_639,C_640))
      | r2_lattice3('#skF_5',B_639,'#skF_2'('#skF_5',B_639,C_640))
      | r1_yellow_0('#skF_5',B_639)
      | ~ r2_lattice3('#skF_5',B_639,C_640)
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4238])).

tff(c_4365,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_4359])).

tff(c_4376,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4365])).

tff(c_4377,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4376])).

tff(c_4225,plain,(
    ! [A_607,B_608,C_609] :
      ( r2_lattice3(A_607,B_608,'#skF_1'(A_607,B_608,C_609))
      | m1_subset_1('#skF_2'(A_607,B_608,C_609),u1_struct_0(A_607))
      | r1_yellow_0(A_607,B_608)
      | ~ r2_lattice3(A_607,B_608,C_609)
      | ~ m1_subset_1(C_609,u1_struct_0(A_607))
      | ~ l1_orders_2(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4229,plain,(
    ! [B_608,C_609] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_608,C_609))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_608,C_609))
      | r2_lattice3('#skF_5',B_608,'#skF_1'('#skF_5',B_608,C_609))
      | r1_yellow_0('#skF_5',B_608)
      | ~ r2_lattice3('#skF_5',B_608,C_609)
      | ~ m1_subset_1(C_609,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4225,c_4175])).

tff(c_4383,plain,(
    ! [B_642,C_643] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_642,C_643))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_642,C_643))
      | r2_lattice3('#skF_5',B_642,'#skF_1'('#skF_5',B_642,C_643))
      | r1_yellow_0('#skF_5',B_642)
      | ~ r2_lattice3('#skF_5',B_642,C_643)
      | ~ m1_subset_1(C_643,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4229])).

tff(c_4385,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4377,c_4383])).

tff(c_4389,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4385])).

tff(c_4260,plain,(
    ! [A_624,B_625,C_626] :
      ( m1_subset_1('#skF_1'(A_624,B_625,C_626),u1_struct_0(A_624))
      | m1_subset_1('#skF_2'(A_624,B_625,C_626),u1_struct_0(A_624))
      | r1_yellow_0(A_624,B_625)
      | ~ r2_lattice3(A_624,B_625,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0(A_624))
      | ~ l1_orders_2(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4264,plain,(
    ! [B_625,C_626] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_625,C_626))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_625,C_626))
      | m1_subset_1('#skF_2'('#skF_5',B_625,C_626),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_625)
      | ~ r2_lattice3('#skF_5',B_625,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4260,c_4175])).

tff(c_4354,plain,(
    ! [B_637,C_638] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_637,C_638))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_637,C_638))
      | m1_subset_1('#skF_2'('#skF_5',B_637,C_638),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_637)
      | ~ r2_lattice3('#skF_5',B_637,C_638)
      | ~ m1_subset_1(C_638,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4264])).

tff(c_4487,plain,(
    ! [B_655,C_656] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_655,C_656))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_655,C_656))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_655,C_656))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_655,C_656))
      | r1_yellow_0('#skF_5',B_655)
      | ~ r2_lattice3('#skF_5',B_655,C_656)
      | ~ m1_subset_1(C_656,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4354,c_4175])).

tff(c_4490,plain,(
    ! [C_58] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4389,c_4487])).

tff(c_4520,plain,(
    ! [C_657] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_657))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_657))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_657))
      | ~ r2_lattice3('#skF_5','#skF_6',C_657)
      | ~ m1_subset_1(C_657,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4490])).

tff(c_4527,plain,(
    ! [C_658] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_658))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_658))
      | ~ r2_lattice3('#skF_5','#skF_6',C_658)
      | ~ m1_subset_1(C_658,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4377,c_4520])).

tff(c_4533,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4527,c_32])).

tff(c_4549,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_4533])).

tff(c_4550,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4549])).

tff(c_4562,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4550])).

tff(c_4587,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4562,c_38])).

tff(c_4590,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4587])).

tff(c_4591,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4311,c_4590])).

tff(c_4593,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4591])).

tff(c_4600,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_4593])).

tff(c_4607,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_4600])).

tff(c_4608,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4607])).

tff(c_4267,plain,(
    ! [B_625,C_626] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_625,C_626))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_625,C_626))
      | m1_subset_1('#skF_2'('#skF_5',B_625,C_626),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_625)
      | ~ r2_lattice3('#skF_5',B_625,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4264])).

tff(c_4597,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4267,c_4593])).

tff(c_4603,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_4597])).

tff(c_4604,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4603])).

tff(c_4636,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4608,c_4604])).

tff(c_4640,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4636,c_32])).

tff(c_4654,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_4640])).

tff(c_4656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4593,c_4654])).

tff(c_4657,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4591])).

tff(c_4867,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4864,c_4657])).

tff(c_4892,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_4867])).

tff(c_4915,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4892,c_20])).

tff(c_4927,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2244,c_4915])).

tff(c_4950,plain,(
    ! [E_681] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_681)
      | ~ r2_lattice3('#skF_5','#skF_6',E_681)
      | ~ m1_subset_1(E_681,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4927])).

tff(c_4953,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4950,c_4657])).

tff(c_4979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_4953])).

tff(c_4981,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4550])).

tff(c_4536,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4527,c_26])).

tff(c_4553,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2244,c_40,c_4536])).

tff(c_4554,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4553])).

tff(c_5009,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_4981,c_4554])).

tff(c_4980,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4550])).

tff(c_4985,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4980,c_4175])).

tff(c_5073,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5009,c_4985])).

tff(c_5074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4981,c_5073])).

tff(c_5075,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5085,plain,(
    ! [A_688,B_689,D_690] :
      ( r1_orders_2(A_688,'#skF_3'(A_688,B_689),D_690)
      | ~ r2_lattice3(A_688,B_689,D_690)
      | ~ m1_subset_1(D_690,u1_struct_0(A_688))
      | ~ r1_yellow_0(A_688,B_689)
      | ~ l1_orders_2(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5076,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_50,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5078,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5076,c_50])).

tff(c_5089,plain,(
    ! [B_689] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_689))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_689),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_689,'#skF_9'('#skF_3'('#skF_5',B_689)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_689)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_689)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5085,c_5078])).

tff(c_5113,plain,(
    ! [B_712] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_712))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_712),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_712,'#skF_9'('#skF_3'('#skF_5',B_712)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_712)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_712) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5089])).

tff(c_5116,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5075,c_5113])).

tff(c_5119,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5116])).

tff(c_5120,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5119])).

tff(c_5123,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_5120])).

tff(c_5127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5123])).

tff(c_5129,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5119])).

tff(c_66,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5081,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5076,c_66])).

tff(c_5128,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5119])).

tff(c_5130,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5128])).

tff(c_5133,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5081,c_5130])).

tff(c_5136,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5129,c_5133])).

tff(c_5144,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5136])).

tff(c_5148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5144])).

tff(c_5149,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5128])).

tff(c_5153,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5149])).

tff(c_5157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5153])).

tff(c_5159,plain,(
    ~ r1_yellow_0('#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_74,plain,
    ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5160,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5159,c_74])).

tff(c_5158,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_5323,plain,(
    ! [A_769,B_770,C_771,E_772] :
      ( m1_subset_1('#skF_1'(A_769,B_770,C_771),u1_struct_0(A_769))
      | r1_orders_2(A_769,'#skF_2'(A_769,B_770,C_771),E_772)
      | ~ r2_lattice3(A_769,B_770,E_772)
      | ~ m1_subset_1(E_772,u1_struct_0(A_769))
      | r1_yellow_0(A_769,B_770)
      | ~ r2_lattice3(A_769,B_770,C_771)
      | ~ m1_subset_1(C_771,u1_struct_0(A_769))
      | ~ l1_orders_2(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5163,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5','#skF_7',D_96)
      | ~ r2_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5159,c_70])).

tff(c_5327,plain,(
    ! [B_770,C_771,E_772] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_770,C_771))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_770,C_771))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_770,C_771),E_772)
      | ~ r2_lattice3('#skF_5',B_770,E_772)
      | ~ m1_subset_1(E_772,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_770)
      | ~ r2_lattice3('#skF_5',B_770,C_771)
      | ~ m1_subset_1(C_771,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5323,c_5163])).

tff(c_5570,plain,(
    ! [B_798,C_799,E_800] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_798,C_799))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_798,C_799))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_798,C_799),E_800)
      | ~ r2_lattice3('#skF_5',B_798,E_800)
      | ~ m1_subset_1(E_800,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_798)
      | ~ r2_lattice3('#skF_5',B_798,C_799)
      | ~ m1_subset_1(C_799,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5327])).

tff(c_5573,plain,(
    ! [C_58,E_800,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_800)
      | ~ r2_lattice3('#skF_5','#skF_6',E_800)
      | ~ m1_subset_1(E_800,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_5570])).

tff(c_5583,plain,(
    ! [C_58,E_800,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_800)
      | ~ r2_lattice3('#skF_5','#skF_6',E_800)
      | ~ m1_subset_1(E_800,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5573])).

tff(c_5584,plain,(
    ! [C_58,E_800,E_64] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_800)
      | ~ r2_lattice3('#skF_5','#skF_6',E_800)
      | ~ m1_subset_1(E_800,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_58),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5583])).

tff(c_5890,plain,(
    ! [C_819,E_820] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_819))
      | ~ r2_lattice3('#skF_5','#skF_6',E_820)
      | ~ m1_subset_1(E_820,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_819)
      | ~ m1_subset_1(C_819,u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6',C_819),E_820) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5584])).

tff(c_5225,plain,(
    ! [A_743,B_744,C_745] :
      ( m1_subset_1('#skF_1'(A_743,B_744,C_745),u1_struct_0(A_743))
      | '#skF_2'(A_743,B_744,C_745) != C_745
      | r1_yellow_0(A_743,B_744)
      | ~ r2_lattice3(A_743,B_744,C_745)
      | ~ m1_subset_1(C_745,u1_struct_0(A_743))
      | ~ l1_orders_2(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5229,plain,(
    ! [B_744,C_745] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_744,C_745))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_744,C_745))
      | '#skF_2'('#skF_5',B_744,C_745) != C_745
      | r1_yellow_0('#skF_5',B_744)
      | ~ r2_lattice3('#skF_5',B_744,C_745)
      | ~ m1_subset_1(C_745,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5225,c_5163])).

tff(c_5276,plain,(
    ! [B_766,C_767] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_766,C_767))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_766,C_767))
      | '#skF_2'('#skF_5',B_766,C_767) != C_767
      | r1_yellow_0('#skF_5',B_766)
      | ~ r2_lattice3('#skF_5',B_766,C_767)
      | ~ m1_subset_1(C_767,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5229])).

tff(c_5286,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_5276])).

tff(c_5293,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | '#skF_2'('#skF_5','#skF_6',C_58) != C_58
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5286])).

tff(c_5295,plain,(
    ! [C_768] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_768))
      | '#skF_2'('#skF_5','#skF_6',C_768) != C_768
      | ~ r2_lattice3('#skF_5','#skF_6',C_768)
      | ~ m1_subset_1(C_768,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5293])).

tff(c_5305,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5295,c_14])).

tff(c_5318,plain,
    ( r1_yellow_0('#skF_5','#skF_6')
    | '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_40,c_5305])).

tff(c_5319,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5318])).

tff(c_5259,plain,(
    ! [A_757,B_758,C_759] :
      ( m1_subset_1('#skF_1'(A_757,B_758,C_759),u1_struct_0(A_757))
      | r2_lattice3(A_757,B_758,'#skF_2'(A_757,B_758,C_759))
      | r1_yellow_0(A_757,B_758)
      | ~ r2_lattice3(A_757,B_758,C_759)
      | ~ m1_subset_1(C_759,u1_struct_0(A_757))
      | ~ l1_orders_2(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5263,plain,(
    ! [B_758,C_759] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_758,C_759))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_758,C_759))
      | r2_lattice3('#skF_5',B_758,'#skF_2'('#skF_5',B_758,C_759))
      | r1_yellow_0('#skF_5',B_758)
      | ~ r2_lattice3('#skF_5',B_758,C_759)
      | ~ m1_subset_1(C_759,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5259,c_5163])).

tff(c_5368,plain,(
    ! [B_780,C_781] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_780,C_781))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_780,C_781))
      | r2_lattice3('#skF_5',B_780,'#skF_2'('#skF_5',B_780,C_781))
      | r1_yellow_0('#skF_5',B_780)
      | ~ r2_lattice3('#skF_5',B_780,C_781)
      | ~ m1_subset_1(C_781,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5263])).

tff(c_5372,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_5368])).

tff(c_5378,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5372])).

tff(c_5379,plain,(
    ! [C_58] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_58))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_58))
      | ~ r2_lattice3('#skF_5','#skF_6',C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5378])).

tff(c_5384,plain,(
    ! [C_782] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_782))
      | r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_782))
      | ~ r2_lattice3('#skF_5','#skF_6',C_782)
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5378])).

tff(c_5268,plain,(
    ! [A_763,B_764,C_765] :
      ( r2_lattice3(A_763,B_764,'#skF_1'(A_763,B_764,C_765))
      | m1_subset_1('#skF_2'(A_763,B_764,C_765),u1_struct_0(A_763))
      | r1_yellow_0(A_763,B_764)
      | ~ r2_lattice3(A_763,B_764,C_765)
      | ~ m1_subset_1(C_765,u1_struct_0(A_763))
      | ~ l1_orders_2(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5272,plain,(
    ! [B_764,C_765] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_764,C_765))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_764,C_765))
      | r2_lattice3('#skF_5',B_764,'#skF_1'('#skF_5',B_764,C_765))
      | r1_yellow_0('#skF_5',B_764)
      | ~ r2_lattice3('#skF_5',B_764,C_765)
      | ~ m1_subset_1(C_765,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5268,c_5163])).

tff(c_5275,plain,(
    ! [B_764,C_765] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_764,C_765))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_764,C_765))
      | r2_lattice3('#skF_5',B_764,'#skF_1'('#skF_5',B_764,C_765))
      | r1_yellow_0('#skF_5',B_764)
      | ~ r2_lattice3('#skF_5',B_764,C_765)
      | ~ m1_subset_1(C_765,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5272])).

tff(c_5386,plain,(
    ! [C_782] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_782))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_782))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_782))
      | ~ r2_lattice3('#skF_5','#skF_6',C_782)
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5384,c_5275])).

tff(c_5389,plain,(
    ! [C_782] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_782))
      | r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6',C_782))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_782))
      | ~ r2_lattice3('#skF_5','#skF_6',C_782)
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5386])).

tff(c_5243,plain,(
    ! [A_752,B_753,C_754] :
      ( m1_subset_1('#skF_1'(A_752,B_753,C_754),u1_struct_0(A_752))
      | m1_subset_1('#skF_2'(A_752,B_753,C_754),u1_struct_0(A_752))
      | r1_yellow_0(A_752,B_753)
      | ~ r2_lattice3(A_752,B_753,C_754)
      | ~ m1_subset_1(C_754,u1_struct_0(A_752))
      | ~ l1_orders_2(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5247,plain,(
    ! [B_753,C_754] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_753,C_754))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_753,C_754))
      | m1_subset_1('#skF_2'('#skF_5',B_753,C_754),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_753)
      | ~ r2_lattice3('#skF_5',B_753,C_754)
      | ~ m1_subset_1(C_754,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5243,c_5163])).

tff(c_5361,plain,(
    ! [B_776,C_777] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_776,C_777))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_776,C_777))
      | m1_subset_1('#skF_2'('#skF_5',B_776,C_777),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_776)
      | ~ r2_lattice3('#skF_5',B_776,C_777)
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5247])).

tff(c_5495,plain,(
    ! [B_794,C_795] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_794,C_795))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_794,C_795))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_794,C_795))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_794,C_795))
      | r1_yellow_0('#skF_5',B_794)
      | ~ r2_lattice3('#skF_5',B_794,C_795)
      | ~ m1_subset_1(C_795,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5361,c_5163])).

tff(c_5502,plain,(
    ! [C_782] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_782))
      | r1_yellow_0('#skF_5','#skF_6')
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_782))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_782))
      | ~ r2_lattice3('#skF_5','#skF_6',C_782)
      | ~ m1_subset_1(C_782,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5389,c_5495])).

tff(c_5528,plain,(
    ! [C_796] :
      ( ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6',C_796))
      | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_796))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_796))
      | ~ r2_lattice3('#skF_5','#skF_6',C_796)
      | ~ m1_subset_1(C_796,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5502])).

tff(c_5535,plain,(
    ! [C_797] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6',C_797))
      | r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6',C_797))
      | ~ r2_lattice3('#skF_5','#skF_6',C_797)
      | ~ m1_subset_1(C_797,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5379,c_5528])).

tff(c_5541,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5535,c_32])).

tff(c_5557,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_40,c_5541])).

tff(c_5558,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5557])).

tff(c_5593,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_5558])).

tff(c_5595,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_5593,c_38])).

tff(c_5598,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5160,c_5595])).

tff(c_5599,plain,
    ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5319,c_5598])).

tff(c_5602,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5599])).

tff(c_5608,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_5602])).

tff(c_5615,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5160,c_5158,c_5608])).

tff(c_5616,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5615])).

tff(c_5250,plain,(
    ! [B_753,C_754] :
      ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5',B_753,C_754))
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_753,C_754))
      | m1_subset_1('#skF_2'('#skF_5',B_753,C_754),u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5',B_753)
      | ~ r2_lattice3('#skF_5',B_753,C_754)
      | ~ m1_subset_1(C_754,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5247])).

tff(c_5605,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5250,c_5602])).

tff(c_5611,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_5605])).

tff(c_5612,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5611])).

tff(c_5644,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5616,c_5612])).

tff(c_5648,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_5644,c_32])).

tff(c_5662,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5160,c_5158,c_5648])).

tff(c_5664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5602,c_5662])).

tff(c_5665,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_5599])).

tff(c_5893,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5890,c_5665])).

tff(c_5918,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_5893])).

tff(c_5941,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5918,c_20])).

tff(c_5953,plain,(
    ! [E_64] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_64)
      | ~ r2_lattice3('#skF_5','#skF_6',E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | r1_yellow_0('#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5160,c_5158,c_5941])).

tff(c_5976,plain,(
    ! [E_821] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_7'),E_821)
      | ~ r2_lattice3('#skF_5','#skF_6',E_821)
      | ~ m1_subset_1(E_821,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5953])).

tff(c_5979,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5976,c_5665])).

tff(c_6005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_5979])).

tff(c_6007,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5558])).

tff(c_5544,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5535,c_26])).

tff(c_5561,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_yellow_0('#skF_5','#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5160,c_5158,c_40,c_5544])).

tff(c_5562,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5561])).

tff(c_6018,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_6007,c_5562])).

tff(c_6006,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5558])).

tff(c_6011,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6006,c_5163])).

tff(c_6082,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_6011])).

tff(c_6083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6007,c_6082])).

tff(c_6084,plain,(
    r1_yellow_0('#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6085,plain,(
    r1_yellow_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_52,plain,(
    ! [C_100] :
      ( ~ r1_yellow_0('#skF_5','#skF_6')
      | r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6092,plain,(
    ! [C_100] :
      ( r2_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6085,c_52])).

tff(c_6100,plain,(
    ! [A_832,B_833,D_834] :
      ( r1_orders_2(A_832,'#skF_3'(A_832,B_833),D_834)
      | ~ r2_lattice3(A_832,B_833,D_834)
      | ~ m1_subset_1(D_834,u1_struct_0(A_832))
      | ~ r1_yellow_0(A_832,B_833)
      | ~ l1_orders_2(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [C_100] :
      ( ~ r1_yellow_0('#skF_5','#skF_6')
      | ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6095,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5',C_100,'#skF_9'(C_100))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6085,c_44])).

tff(c_6104,plain,(
    ! [B_833] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_833))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_833),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_833,'#skF_9'('#skF_3'('#skF_5',B_833)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_833)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_833)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6100,c_6095])).

tff(c_6134,plain,(
    ! [B_862] :
      ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_862))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_862),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5',B_862,'#skF_9'('#skF_3'('#skF_5',B_862)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_862)),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_862) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6104])).

tff(c_6137,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6092,c_6134])).

tff(c_6140,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6084,c_6137])).

tff(c_6141,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6140])).

tff(c_6144,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_6141])).

tff(c_6148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6084,c_6144])).

tff(c_6150,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6140])).

tff(c_60,plain,(
    ! [C_100] :
      ( ~ r1_yellow_0('#skF_5','#skF_6')
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6098,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6085,c_60])).

tff(c_6149,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6140])).

tff(c_6151,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6149])).

tff(c_6154,plain,
    ( ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6098,c_6151])).

tff(c_6157,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6150,c_6154])).

tff(c_6161,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6157])).

tff(c_6165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6084,c_6161])).

tff(c_6166,plain,(
    ~ r2_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6149])).

tff(c_6170,plain,
    ( ~ r1_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6166])).

tff(c_6174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6084,c_6170])).

%------------------------------------------------------------------------------
