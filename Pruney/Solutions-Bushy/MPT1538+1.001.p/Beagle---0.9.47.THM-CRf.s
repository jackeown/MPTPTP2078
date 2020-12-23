%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1538+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:01 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :  504 (2574 expanded)
%              Number of leaves         :   22 ( 810 expanded)
%              Depth                    :   21
%              Number of atoms          : 2437 (13578 expanded)
%              Number of equality atoms :  173 ( 455 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > m1_subset_1 > v5_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_9 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8

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
            ( r2_yellow_0(A,B)
          <=> ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r1_lattice3(A,B,E)
                           => r1_orders_2(A,E,D) ) ) )
                   => D = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_6')
    | r2_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_75,plain,(
    ~ r2_yellow_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_72,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_76,plain,(
    r2_yellow_0('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_4,plain,(
    ! [A_1,B_39] :
      ( r1_lattice3(A_1,B_39,'#skF_3'(A_1,B_39))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_39] :
      ( m1_subset_1('#skF_3'(A_1,B_39),u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_7')
      | r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_85,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_16,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1296,plain,(
    ! [A_277,B_278,C_279] :
      ( m1_subset_1('#skF_1'(A_277,B_278,C_279),u1_struct_0(A_277))
      | '#skF_2'(A_277,B_278,C_279) != C_279
      | r2_yellow_0(A_277,B_278)
      | ~ r1_lattice3(A_277,B_278,C_279)
      | ~ m1_subset_1(C_279,u1_struct_0(A_277))
      | ~ l1_orders_2(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_211,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1('#skF_1'(A_155,B_156,C_157),u1_struct_0(A_155))
      | '#skF_2'(A_155,B_156,C_157) != C_157
      | r2_yellow_0(A_155,B_156)
      | ~ r1_lattice3(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    ! [D_96,C_100] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_109,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_89,plain,(
    ! [A_107,D_108,B_109] :
      ( r1_orders_2(A_107,D_108,'#skF_3'(A_107,B_109))
      | ~ r1_lattice3(A_107,B_109,D_108)
      | ~ m1_subset_1(D_108,u1_struct_0(A_107))
      | ~ r2_yellow_0(A_107,B_109)
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_93,plain,(
    ! [B_109] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_109))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_109),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_109,'#skF_9'('#skF_3'('#skF_5',B_109)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_109)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_109)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_89,c_83])).

tff(c_124,plain,(
    ! [B_142] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_142))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_142),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_142,'#skF_9'('#skF_3'('#skF_5',B_142)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_142)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_93])).

tff(c_127,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_109,c_124])).

tff(c_130,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127])).

tff(c_131,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
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
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_139,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_141,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_144,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_110,c_141])).

tff(c_147,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_144])).

tff(c_155,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_155])).

tff(c_160,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_164,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_164])).

tff(c_169,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_215,plain,(
    ! [B_156,C_157] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_156,C_157),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_156,C_157))
      | '#skF_2'('#skF_5',B_156,C_157) != C_157
      | r2_yellow_0('#skF_5',B_156)
      | ~ r1_lattice3('#skF_5',B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_211,c_169])).

tff(c_351,plain,(
    ! [B_187,C_188] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_187,C_188),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_187,C_188))
      | '#skF_2'('#skF_5',B_187,C_188) != C_188
      | r2_yellow_0('#skF_5',B_187)
      | ~ r1_lattice3('#skF_5',B_187,C_188)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_215])).

tff(c_14,plain,(
    ! [A_1,B_39,C_58] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_39,C_58),C_58)
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_361,plain,(
    ! [B_187] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_187,'#skF_7'))
      | '#skF_2'('#skF_5',B_187,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_187)
      | ~ r1_lattice3('#skF_5',B_187,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_351,c_14])).

tff(c_376,plain,(
    ! [B_189] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_189,'#skF_7'))
      | '#skF_2'('#skF_5',B_189,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_189)
      | ~ r1_lattice3('#skF_5',B_189,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_361])).

tff(c_388,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_376])).

tff(c_395,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_388])).

tff(c_396,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_395])).

tff(c_28,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r1_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_314,plain,(
    ! [A_180,B_181,C_182] :
      ( m1_subset_1('#skF_1'(A_180,B_181,C_182),u1_struct_0(A_180))
      | r1_lattice3(A_180,B_181,'#skF_2'(A_180,B_181,C_182))
      | r2_yellow_0(A_180,B_181)
      | ~ r1_lattice3(A_180,B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_318,plain,(
    ! [B_181,C_182] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_181,C_182),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_181,C_182))
      | r1_lattice3('#skF_5',B_181,'#skF_2'('#skF_5',B_181,C_182))
      | r2_yellow_0('#skF_5',B_181)
      | ~ r1_lattice3('#skF_5',B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_314,c_169])).

tff(c_411,plain,(
    ! [B_193,C_194] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_193,C_194),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_193,C_194))
      | r1_lattice3('#skF_5',B_193,'#skF_2'('#skF_5',B_193,C_194))
      | r2_yellow_0('#skF_5',B_193)
      | ~ r1_lattice3('#skF_5',B_193,C_194)
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_318])).

tff(c_26,plain,(
    ! [A_1,B_39,C_58] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_39,C_58),C_58)
      | r1_lattice3(A_1,B_39,'#skF_2'(A_1,B_39,C_58))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_417,plain,(
    ! [B_193] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_193,'#skF_7'))
      | r1_lattice3('#skF_5',B_193,'#skF_2'('#skF_5',B_193,'#skF_7'))
      | r2_yellow_0('#skF_5',B_193)
      | ~ r1_lattice3('#skF_5',B_193,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_411,c_26])).

tff(c_436,plain,(
    ! [B_195] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_195,'#skF_7'))
      | r1_lattice3('#skF_5',B_195,'#skF_2'('#skF_5',B_195,'#skF_7'))
      | r2_yellow_0('#skF_5',B_195)
      | ~ r1_lattice3('#skF_5',B_195,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_417])).

tff(c_440,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_436])).

tff(c_447,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_440])).

tff(c_448,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_447])).

tff(c_22,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | r1_orders_2(A_1,E_64,'#skF_2'(A_1,B_39,C_58))
      | ~ r1_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_1,B_39,C_58] :
      ( r1_lattice3(A_1,B_39,'#skF_1'(A_1,B_39,C_58))
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_265,plain,(
    ! [A_162,B_163,C_164] :
      ( r1_lattice3(A_162,B_163,'#skF_1'(A_162,B_163,C_164))
      | m1_subset_1('#skF_2'(A_162,B_163,C_164),u1_struct_0(A_162))
      | r2_yellow_0(A_162,B_163)
      | ~ r1_lattice3(A_162,B_163,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_269,plain,(
    ! [B_163,C_164] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_163,C_164),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_163,C_164))
      | r1_lattice3('#skF_5',B_163,'#skF_1'('#skF_5',B_163,C_164))
      | r2_yellow_0('#skF_5',B_163)
      | ~ r1_lattice3('#skF_5',B_163,C_164)
      | ~ m1_subset_1(C_164,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_265,c_169])).

tff(c_523,plain,(
    ! [B_204,C_205] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_204,C_205),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_204,C_205))
      | r1_lattice3('#skF_5',B_204,'#skF_1'('#skF_5',B_204,C_205))
      | r2_yellow_0('#skF_5',B_204)
      | ~ r1_lattice3('#skF_5',B_204,C_205)
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_269])).

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

tff(c_525,plain,(
    ! [B_204,C_205] :
      ( '#skF_2'('#skF_5',B_204,C_205) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_204,C_205))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_204,C_205),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_204,C_205))
      | r1_lattice3('#skF_5',B_204,'#skF_1'('#skF_5',B_204,C_205))
      | r2_yellow_0('#skF_5',B_204)
      | ~ r1_lattice3('#skF_5',B_204,C_205)
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_523,c_38])).

tff(c_1208,plain,(
    ! [B_263,C_264] :
      ( '#skF_2'('#skF_5',B_263,C_264) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_263,C_264))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_263,C_264),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_263,C_264))
      | r1_lattice3('#skF_5',B_263,'#skF_1'('#skF_5',B_263,C_264))
      | r2_yellow_0('#skF_5',B_263)
      | ~ r1_lattice3('#skF_5',B_263,C_264)
      | ~ m1_subset_1(C_264,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_525])).

tff(c_1213,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_1208])).

tff(c_1218,plain,(
    ! [B_265,C_266] :
      ( '#skF_2'('#skF_5',B_265,C_266) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_265,C_266))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_265,C_266))
      | r1_lattice3('#skF_5',B_265,'#skF_1'('#skF_5',B_265,C_266))
      | r2_yellow_0('#skF_5',B_265)
      | ~ r1_lattice3('#skF_5',B_265,C_266)
      | ~ m1_subset_1(C_266,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1213])).

tff(c_1226,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1218])).

tff(c_1233,plain,(
    ! [B_267,C_268] :
      ( '#skF_2'('#skF_5',B_267,C_268) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_267,C_268))
      | r1_lattice3('#skF_5',B_267,'#skF_1'('#skF_5',B_267,C_268))
      | ~ r1_lattice3('#skF_5',B_267,'#skF_7')
      | r2_yellow_0('#skF_5',B_267)
      | ~ r1_lattice3('#skF_5',B_267,C_268)
      | ~ m1_subset_1(C_268,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_1226])).

tff(c_1235,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_448,c_1233])).

tff(c_1240,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_1235])).

tff(c_1241,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_396,c_1240])).

tff(c_453,plain,(
    ! [A_196,B_197,C_198,E_199] :
      ( m1_subset_1('#skF_1'(A_196,B_197,C_198),u1_struct_0(A_196))
      | r1_orders_2(A_196,E_199,'#skF_2'(A_196,B_197,C_198))
      | ~ r1_lattice3(A_196,B_197,E_199)
      | ~ m1_subset_1(E_199,u1_struct_0(A_196))
      | r2_yellow_0(A_196,B_197)
      | ~ r1_lattice3(A_196,B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ l1_orders_2(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_457,plain,(
    ! [B_197,C_198,E_199] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_197,C_198),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_197,C_198))
      | r1_orders_2('#skF_5',E_199,'#skF_2'('#skF_5',B_197,C_198))
      | ~ r1_lattice3('#skF_5',B_197,E_199)
      | ~ m1_subset_1(E_199,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_197)
      | ~ r1_lattice3('#skF_5',B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_453,c_169])).

tff(c_574,plain,(
    ! [B_212,C_213,E_214] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_212,C_213),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_212,C_213))
      | r1_orders_2('#skF_5',E_214,'#skF_2'('#skF_5',B_212,C_213))
      | ~ r1_lattice3('#skF_5',B_212,E_214)
      | ~ m1_subset_1(E_214,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_212)
      | ~ r1_lattice3('#skF_5',B_212,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_457])).

tff(c_20,plain,(
    ! [A_1,B_39,C_58,E_64] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_39,C_58),C_58)
      | r1_orders_2(A_1,E_64,'#skF_2'(A_1,B_39,C_58))
      | ~ r1_lattice3(A_1,B_39,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_577,plain,(
    ! [E_64,B_212,E_214] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_212,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_212,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_212,'#skF_7'))
      | r1_orders_2('#skF_5',E_214,'#skF_2'('#skF_5',B_212,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_212,E_214)
      | ~ m1_subset_1(E_214,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_212)
      | ~ r1_lattice3('#skF_5',B_212,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_574,c_20])).

tff(c_618,plain,(
    ! [E_64,B_212,E_214] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_212,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_212,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_212,'#skF_7'))
      | r1_orders_2('#skF_5',E_214,'#skF_2'('#skF_5',B_212,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_212,E_214)
      | ~ m1_subset_1(E_214,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_212)
      | ~ r1_lattice3('#skF_5',B_212,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_577])).

tff(c_1062,plain,(
    ! [B_254,E_255] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_254,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_254,E_255)
      | ~ m1_subset_1(E_255,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_254)
      | ~ r1_lattice3('#skF_5',B_254,'#skF_7')
      | r1_orders_2('#skF_5',E_255,'#skF_2'('#skF_5',B_254,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_618])).

tff(c_274,plain,(
    ! [A_165,B_166,C_167] :
      ( m1_subset_1('#skF_1'(A_165,B_166,C_167),u1_struct_0(A_165))
      | m1_subset_1('#skF_2'(A_165,B_166,C_167),u1_struct_0(A_165))
      | r2_yellow_0(A_165,B_166)
      | ~ r1_lattice3(A_165,B_166,C_167)
      | ~ m1_subset_1(C_167,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_278,plain,(
    ! [B_166,C_167] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_166,C_167),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_166,C_167))
      | m1_subset_1('#skF_2'('#skF_5',B_166,C_167),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_166)
      | ~ r1_lattice3('#skF_5',B_166,C_167)
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_274,c_169])).

tff(c_281,plain,(
    ! [B_166,C_167] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_166,C_167),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_166,C_167))
      | m1_subset_1('#skF_2'('#skF_5',B_166,C_167),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_166)
      | ~ r1_lattice3('#skF_5',B_166,C_167)
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_278])).

tff(c_493,plain,(
    ! [B_200,C_201] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_200,C_201),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_200,C_201))
      | m1_subset_1('#skF_2'('#skF_5',B_200,C_201),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_200)
      | ~ r1_lattice3('#skF_5',B_200,C_201)
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_278])).

tff(c_498,plain,(
    ! [B_202,C_203] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_202,C_203),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_202,C_203))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_202,C_203),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_202,C_203))
      | r2_yellow_0('#skF_5',B_202)
      | ~ r1_lattice3('#skF_5',B_202,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_493,c_169])).

tff(c_32,plain,(
    ! [A_1,B_39,C_58] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_39,C_58),C_58)
      | m1_subset_1('#skF_2'(A_1,B_39,C_58),u1_struct_0(A_1))
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_501,plain,(
    ! [B_202] :
      ( m1_subset_1('#skF_2'('#skF_5',B_202,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_202,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_202,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_202,'#skF_7'))
      | r2_yellow_0('#skF_5',B_202)
      | ~ r1_lattice3('#skF_5',B_202,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_498,c_32])).

tff(c_563,plain,(
    ! [B_210] :
      ( m1_subset_1('#skF_2'('#skF_5',B_210,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_210,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_210,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_210,'#skF_7'))
      | r2_yellow_0('#skF_5',B_210)
      | ~ r1_lattice3('#skF_5',B_210,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_501])).

tff(c_568,plain,(
    ! [B_211] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_211,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_211,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_211,'#skF_7'))
      | r2_yellow_0('#skF_5',B_211)
      | ~ r1_lattice3('#skF_5',B_211,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_563,c_169])).

tff(c_570,plain,(
    ! [B_211] :
      ( '#skF_2'('#skF_5',B_211,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_211,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_211,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_211,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_211,'#skF_7'))
      | r2_yellow_0('#skF_5',B_211)
      | ~ r1_lattice3('#skF_5',B_211,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_568,c_38])).

tff(c_717,plain,(
    ! [B_223] :
      ( '#skF_2'('#skF_5',B_223,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_223,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_223,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_223,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_223,'#skF_7'))
      | r2_yellow_0('#skF_5',B_223)
      | ~ r1_lattice3('#skF_5',B_223,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_570])).

tff(c_724,plain,(
    ! [B_166] :
      ( '#skF_2'('#skF_5',B_166,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_166,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_166,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_166,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_166,'#skF_7'))
      | r2_yellow_0('#skF_5',B_166)
      | ~ r1_lattice3('#skF_5',B_166,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_281,c_717])).

tff(c_742,plain,(
    ! [B_226] :
      ( '#skF_2'('#skF_5',B_226,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_226,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_226,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_226,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_226,'#skF_7'))
      | r2_yellow_0('#skF_5',B_226)
      | ~ r1_lattice3('#skF_5',B_226,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_724])).

tff(c_746,plain,(
    ! [B_226] :
      ( m1_subset_1('#skF_2'('#skF_5',B_226,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_226,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_226,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_226,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_226,'#skF_7'))
      | r2_yellow_0('#skF_5',B_226)
      | ~ r1_lattice3('#skF_5',B_226,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_742,c_32])).

tff(c_797,plain,(
    ! [B_229] :
      ( m1_subset_1('#skF_2'('#skF_5',B_229,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_229,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_229,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_229,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_229,'#skF_7'))
      | r2_yellow_0('#skF_5',B_229)
      | ~ r1_lattice3('#skF_5',B_229,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_746])).

tff(c_573,plain,(
    ! [B_211] :
      ( '#skF_2'('#skF_5',B_211,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_211,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_211,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_211,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_211,'#skF_7'))
      | r2_yellow_0('#skF_5',B_211)
      | ~ r1_lattice3('#skF_5',B_211,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_570])).

tff(c_804,plain,(
    ! [B_229] :
      ( '#skF_2'('#skF_5',B_229,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_229,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_229,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_229,'#skF_7'))
      | r2_yellow_0('#skF_5',B_229)
      | ~ r1_lattice3('#skF_5',B_229,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_797,c_573])).

tff(c_1066,plain,(
    ! [B_254] :
      ( '#skF_2'('#skF_5',B_254,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_254,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_254,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_254)
      | ~ r1_lattice3('#skF_5',B_254,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1062,c_804])).

tff(c_1095,plain,(
    ! [B_254] :
      ( '#skF_2'('#skF_5',B_254,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_254,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_254,'#skF_7'))
      | r2_yellow_0('#skF_5',B_254)
      | ~ r1_lattice3('#skF_5',B_254,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1066])).

tff(c_1244,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1241,c_1095])).

tff(c_1252,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_448,c_1244])).

tff(c_1254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_396,c_1252])).

tff(c_1255,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1300,plain,(
    ! [B_278,C_279] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_278,C_279),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_278,C_279))
      | '#skF_2'('#skF_5',B_278,C_279) != C_279
      | r2_yellow_0('#skF_5',B_278)
      | ~ r1_lattice3('#skF_5',B_278,C_279)
      | ~ m1_subset_1(C_279,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1296,c_1255])).

tff(c_1377,plain,(
    ! [B_304,C_305] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_304,C_305),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_304,C_305))
      | '#skF_2'('#skF_5',B_304,C_305) != C_305
      | r2_yellow_0('#skF_5',B_304)
      | ~ r1_lattice3('#skF_5',B_304,C_305)
      | ~ m1_subset_1(C_305,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1300])).

tff(c_1387,plain,(
    ! [B_304] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_304,'#skF_7'))
      | '#skF_2'('#skF_5',B_304,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_304)
      | ~ r1_lattice3('#skF_5',B_304,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1377,c_14])).

tff(c_1410,plain,(
    ! [B_307] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_307,'#skF_7'))
      | '#skF_2'('#skF_5',B_307,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_307)
      | ~ r1_lattice3('#skF_5',B_307,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_1387])).

tff(c_1420,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_1410])).

tff(c_1427,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_1420])).

tff(c_1428,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1427])).

tff(c_1329,plain,(
    ! [A_284,B_285,C_286] :
      ( m1_subset_1('#skF_1'(A_284,B_285,C_286),u1_struct_0(A_284))
      | r1_lattice3(A_284,B_285,'#skF_2'(A_284,B_285,C_286))
      | r2_yellow_0(A_284,B_285)
      | ~ r1_lattice3(A_284,B_285,C_286)
      | ~ m1_subset_1(C_286,u1_struct_0(A_284))
      | ~ l1_orders_2(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1333,plain,(
    ! [B_285,C_286] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_285,C_286),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_285,C_286))
      | r1_lattice3('#skF_5',B_285,'#skF_2'('#skF_5',B_285,C_286))
      | r2_yellow_0('#skF_5',B_285)
      | ~ r1_lattice3('#skF_5',B_285,C_286)
      | ~ m1_subset_1(C_286,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1329,c_1255])).

tff(c_1463,plain,(
    ! [B_319,C_320] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_319,C_320),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_319,C_320))
      | r1_lattice3('#skF_5',B_319,'#skF_2'('#skF_5',B_319,C_320))
      | r2_yellow_0('#skF_5',B_319)
      | ~ r1_lattice3('#skF_5',B_319,C_320)
      | ~ m1_subset_1(C_320,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1333])).

tff(c_1472,plain,(
    ! [B_319] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_319,'#skF_7'))
      | r1_lattice3('#skF_5',B_319,'#skF_2'('#skF_5',B_319,'#skF_7'))
      | r2_yellow_0('#skF_5',B_319)
      | ~ r1_lattice3('#skF_5',B_319,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1463,c_26])).

tff(c_1494,plain,(
    ! [B_321] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_321,'#skF_7'))
      | r1_lattice3('#skF_5',B_321,'#skF_2'('#skF_5',B_321,'#skF_7'))
      | r2_yellow_0('#skF_5',B_321)
      | ~ r1_lattice3('#skF_5',B_321,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_1472])).

tff(c_1499,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1494])).

tff(c_1505,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_85,c_1499])).

tff(c_1506,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1505])).

tff(c_1351,plain,(
    ! [A_296,B_297,C_298] :
      ( r1_lattice3(A_296,B_297,'#skF_1'(A_296,B_297,C_298))
      | m1_subset_1('#skF_2'(A_296,B_297,C_298),u1_struct_0(A_296))
      | r2_yellow_0(A_296,B_297)
      | ~ r1_lattice3(A_296,B_297,C_298)
      | ~ m1_subset_1(C_298,u1_struct_0(A_296))
      | ~ l1_orders_2(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1355,plain,(
    ! [B_297,C_298] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_297,C_298),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_297,C_298))
      | r1_lattice3('#skF_5',B_297,'#skF_1'('#skF_5',B_297,C_298))
      | r2_yellow_0('#skF_5',B_297)
      | ~ r1_lattice3('#skF_5',B_297,C_298)
      | ~ m1_subset_1(C_298,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1351,c_1255])).

tff(c_1450,plain,(
    ! [B_315,C_316] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_315,C_316),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_315,C_316))
      | r1_lattice3('#skF_5',B_315,'#skF_1'('#skF_5',B_315,C_316))
      | r2_yellow_0('#skF_5',B_315)
      | ~ r1_lattice3('#skF_5',B_315,C_316)
      | ~ m1_subset_1(C_316,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1355])).

tff(c_1452,plain,(
    ! [B_315,C_316] :
      ( '#skF_2'('#skF_5',B_315,C_316) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_315,C_316))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_315,C_316),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_315,C_316))
      | r1_lattice3('#skF_5',B_315,'#skF_1'('#skF_5',B_315,C_316))
      | r2_yellow_0('#skF_5',B_315)
      | ~ r1_lattice3('#skF_5',B_315,C_316)
      | ~ m1_subset_1(C_316,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1450,c_38])).

tff(c_2233,plain,(
    ! [B_382,C_383] :
      ( '#skF_2'('#skF_5',B_382,C_383) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_382,C_383))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_382,C_383),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_382,C_383))
      | r1_lattice3('#skF_5',B_382,'#skF_1'('#skF_5',B_382,C_383))
      | r2_yellow_0('#skF_5',B_382)
      | ~ r1_lattice3('#skF_5',B_382,C_383)
      | ~ m1_subset_1(C_383,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_1452])).

tff(c_2238,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_2233])).

tff(c_2243,plain,(
    ! [B_384,C_385] :
      ( '#skF_2'('#skF_5',B_384,C_385) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_384,C_385))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_384,C_385))
      | r1_lattice3('#skF_5',B_384,'#skF_1'('#skF_5',B_384,C_385))
      | r2_yellow_0('#skF_5',B_384)
      | ~ r1_lattice3('#skF_5',B_384,C_385)
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2238])).

tff(c_2250,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_2243])).

tff(c_2258,plain,(
    ! [B_386,C_387] :
      ( '#skF_2'('#skF_5',B_386,C_387) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_386,C_387))
      | r1_lattice3('#skF_5',B_386,'#skF_1'('#skF_5',B_386,C_387))
      | ~ r1_lattice3('#skF_5',B_386,'#skF_7')
      | r2_yellow_0('#skF_5',B_386)
      | ~ r1_lattice3('#skF_5',B_386,C_387)
      | ~ m1_subset_1(C_387,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2250])).

tff(c_2260,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1506,c_2258])).

tff(c_2265,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_85,c_2260])).

tff(c_2266,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1428,c_2265])).

tff(c_1511,plain,(
    ! [A_322,B_323,C_324,E_325] :
      ( m1_subset_1('#skF_1'(A_322,B_323,C_324),u1_struct_0(A_322))
      | r1_orders_2(A_322,E_325,'#skF_2'(A_322,B_323,C_324))
      | ~ r1_lattice3(A_322,B_323,E_325)
      | ~ m1_subset_1(E_325,u1_struct_0(A_322))
      | r2_yellow_0(A_322,B_323)
      | ~ r1_lattice3(A_322,B_323,C_324)
      | ~ m1_subset_1(C_324,u1_struct_0(A_322))
      | ~ l1_orders_2(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1515,plain,(
    ! [B_323,C_324,E_325] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_323,C_324),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_323,C_324))
      | r1_orders_2('#skF_5',E_325,'#skF_2'('#skF_5',B_323,C_324))
      | ~ r1_lattice3('#skF_5',B_323,E_325)
      | ~ m1_subset_1(E_325,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_323)
      | ~ r1_lattice3('#skF_5',B_323,C_324)
      | ~ m1_subset_1(C_324,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1511,c_1255])).

tff(c_1637,plain,(
    ! [B_334,C_335,E_336] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_334,C_335),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_334,C_335))
      | r1_orders_2('#skF_5',E_336,'#skF_2'('#skF_5',B_334,C_335))
      | ~ r1_lattice3('#skF_5',B_334,E_336)
      | ~ m1_subset_1(E_336,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_334)
      | ~ r1_lattice3('#skF_5',B_334,C_335)
      | ~ m1_subset_1(C_335,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1515])).

tff(c_1640,plain,(
    ! [E_64,B_334,E_336] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_334,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_334,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_334,'#skF_7'))
      | r1_orders_2('#skF_5',E_336,'#skF_2'('#skF_5',B_334,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_334,E_336)
      | ~ m1_subset_1(E_336,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_334)
      | ~ r1_lattice3('#skF_5',B_334,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1637,c_20])).

tff(c_1681,plain,(
    ! [E_64,B_334,E_336] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_334,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_334,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_334,'#skF_7'))
      | r1_orders_2('#skF_5',E_336,'#skF_2'('#skF_5',B_334,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_334,E_336)
      | ~ m1_subset_1(E_336,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_334)
      | ~ r1_lattice3('#skF_5',B_334,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_1640])).

tff(c_2092,plain,(
    ! [B_373,E_374] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_373,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_373,E_374)
      | ~ m1_subset_1(E_374,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_373)
      | ~ r1_lattice3('#skF_5',B_373,'#skF_7')
      | r1_orders_2('#skF_5',E_374,'#skF_2'('#skF_5',B_373,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1681])).

tff(c_1338,plain,(
    ! [A_290,B_291,C_292] :
      ( m1_subset_1('#skF_1'(A_290,B_291,C_292),u1_struct_0(A_290))
      | m1_subset_1('#skF_2'(A_290,B_291,C_292),u1_struct_0(A_290))
      | r2_yellow_0(A_290,B_291)
      | ~ r1_lattice3(A_290,B_291,C_292)
      | ~ m1_subset_1(C_292,u1_struct_0(A_290))
      | ~ l1_orders_2(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1342,plain,(
    ! [B_291,C_292] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_291,C_292),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_291,C_292))
      | m1_subset_1('#skF_2'('#skF_5',B_291,C_292),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_291)
      | ~ r1_lattice3('#skF_5',B_291,C_292)
      | ~ m1_subset_1(C_292,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1338,c_1255])).

tff(c_1345,plain,(
    ! [B_291,C_292] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_291,C_292),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_291,C_292))
      | m1_subset_1('#skF_2'('#skF_5',B_291,C_292),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_291)
      | ~ r1_lattice3('#skF_5',B_291,C_292)
      | ~ m1_subset_1(C_292,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1342])).

tff(c_1458,plain,(
    ! [B_317,C_318] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_317,C_318),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_317,C_318))
      | m1_subset_1('#skF_2'('#skF_5',B_317,C_318),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_317)
      | ~ r1_lattice3('#skF_5',B_317,C_318)
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1342])).

tff(c_1595,plain,(
    ! [B_330,C_331] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_330,C_331),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_330,C_331))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_330,C_331),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_330,C_331))
      | r2_yellow_0('#skF_5',B_330)
      | ~ r1_lattice3('#skF_5',B_330,C_331)
      | ~ m1_subset_1(C_331,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1458,c_1255])).

tff(c_1601,plain,(
    ! [B_330] :
      ( m1_subset_1('#skF_2'('#skF_5',B_330,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_330,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_330,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_330,'#skF_7'))
      | r2_yellow_0('#skF_5',B_330)
      | ~ r1_lattice3('#skF_5',B_330,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1595,c_32])).

tff(c_1626,plain,(
    ! [B_332] :
      ( m1_subset_1('#skF_2'('#skF_5',B_332,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_332,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_332,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_332,'#skF_7'))
      | r2_yellow_0('#skF_5',B_332)
      | ~ r1_lattice3('#skF_5',B_332,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_1601])).

tff(c_1631,plain,(
    ! [B_333] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_333,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_333,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_333,'#skF_7'))
      | r2_yellow_0('#skF_5',B_333)
      | ~ r1_lattice3('#skF_5',B_333,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1626,c_1255])).

tff(c_1633,plain,(
    ! [B_333] :
      ( '#skF_2'('#skF_5',B_333,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_333,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_333,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_333,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_333,'#skF_7'))
      | r2_yellow_0('#skF_5',B_333)
      | ~ r1_lattice3('#skF_5',B_333,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1631,c_38])).

tff(c_1774,plain,(
    ! [B_342] :
      ( '#skF_2'('#skF_5',B_342,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_342,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_342,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_342,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_342,'#skF_7'))
      | r2_yellow_0('#skF_5',B_342)
      | ~ r1_lattice3('#skF_5',B_342,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_1633])).

tff(c_1781,plain,(
    ! [B_291] :
      ( '#skF_2'('#skF_5',B_291,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_291,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_291,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_291,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_291,'#skF_7'))
      | r2_yellow_0('#skF_5',B_291)
      | ~ r1_lattice3('#skF_5',B_291,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1345,c_1774])).

tff(c_1793,plain,(
    ! [B_343] :
      ( '#skF_2'('#skF_5',B_343,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_343,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_343,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_343,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_343,'#skF_7'))
      | r2_yellow_0('#skF_5',B_343)
      | ~ r1_lattice3('#skF_5',B_343,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1781])).

tff(c_1797,plain,(
    ! [B_343] :
      ( m1_subset_1('#skF_2'('#skF_5',B_343,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_343,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_343,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_343,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_343,'#skF_7'))
      | r2_yellow_0('#skF_5',B_343)
      | ~ r1_lattice3('#skF_5',B_343,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1793,c_32])).

tff(c_1854,plain,(
    ! [B_349] :
      ( m1_subset_1('#skF_2'('#skF_5',B_349,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_349,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_349,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_349,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_349,'#skF_7'))
      | r2_yellow_0('#skF_5',B_349)
      | ~ r1_lattice3('#skF_5',B_349,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_1797])).

tff(c_1636,plain,(
    ! [B_333] :
      ( '#skF_2'('#skF_5',B_333,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_333,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_333,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_333,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_333,'#skF_7'))
      | r2_yellow_0('#skF_5',B_333)
      | ~ r1_lattice3('#skF_5',B_333,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_1633])).

tff(c_1861,plain,(
    ! [B_349] :
      ( '#skF_2'('#skF_5',B_349,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_349,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_349,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_349,'#skF_7'))
      | r2_yellow_0('#skF_5',B_349)
      | ~ r1_lattice3('#skF_5',B_349,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1854,c_1636])).

tff(c_2096,plain,(
    ! [B_373] :
      ( '#skF_2'('#skF_5',B_373,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_373,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_373,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_373)
      | ~ r1_lattice3('#skF_5',B_373,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2092,c_1861])).

tff(c_2125,plain,(
    ! [B_373] :
      ( '#skF_2'('#skF_5',B_373,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_373,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_373,'#skF_7'))
      | r2_yellow_0('#skF_5',B_373)
      | ~ r1_lattice3('#skF_5',B_373,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2096])).

tff(c_2269,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2266,c_2125])).

tff(c_2277,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1506,c_2269])).

tff(c_2279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1428,c_2277])).

tff(c_2280,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2286,plain,(
    ! [A_390,D_391,B_392] :
      ( r1_orders_2(A_390,D_391,'#skF_3'(A_390,B_392))
      | ~ r1_lattice3(A_390,B_392,D_391)
      | ~ m1_subset_1(D_391,u1_struct_0(A_390))
      | ~ r2_yellow_0(A_390,B_392)
      | ~ l1_orders_2(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2290,plain,(
    ! [B_392] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_392))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_392),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_392,'#skF_9'('#skF_3'('#skF_5',B_392)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_392)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_392)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2286,c_83])).

tff(c_2308,plain,(
    ! [B_411] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_411))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_411),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_411,'#skF_9'('#skF_3'('#skF_5',B_411)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_411)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2290])).

tff(c_2311,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2280,c_2308])).

tff(c_2314,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2311])).

tff(c_2315,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2314])).

tff(c_2318,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2315])).

tff(c_2322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2318])).

tff(c_2324,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2314])).

tff(c_2281,plain,(
    ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_64,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_6','#skF_7')
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2284,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2281,c_64])).

tff(c_2323,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2314])).

tff(c_2325,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2323])).

tff(c_2328,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2284,c_2325])).

tff(c_2331,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2324,c_2328])).

tff(c_2340,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2331])).

tff(c_2344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2340])).

tff(c_2345,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_2349,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2345])).

tff(c_2353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2349])).

tff(c_2354,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4572,plain,(
    ! [A_683,B_684,C_685] :
      ( m1_subset_1('#skF_1'(A_683,B_684,C_685),u1_struct_0(A_683))
      | '#skF_2'(A_683,B_684,C_685) != C_685
      | r2_yellow_0(A_683,B_684)
      | ~ r1_lattice3(A_683,B_684,C_685)
      | ~ m1_subset_1(C_685,u1_struct_0(A_683))
      | ~ l1_orders_2(A_683) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3525,plain,(
    ! [A_570,B_571,C_572] :
      ( m1_subset_1('#skF_1'(A_570,B_571,C_572),u1_struct_0(A_570))
      | '#skF_2'(A_570,B_571,C_572) != C_572
      | r2_yellow_0(A_570,B_571)
      | ~ r1_lattice3(A_570,B_571,C_572)
      | ~ m1_subset_1(C_572,u1_struct_0(A_570))
      | ~ l1_orders_2(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_1,B_39,C_58] :
      ( m1_subset_1('#skF_1'(A_1,B_39,C_58),u1_struct_0(A_1))
      | '#skF_2'(A_1,B_39,C_58) != C_58
      | r2_yellow_0(A_1,B_39)
      | ~ r1_lattice3(A_1,B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2372,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1,D_69,B_39] :
      ( r1_orders_2(A_1,D_69,'#skF_3'(A_1,B_39))
      | ~ r1_lattice3(A_1,B_39,D_69)
      | ~ m1_subset_1(D_69,u1_struct_0(A_1))
      | ~ r2_yellow_0(A_1,B_39)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [D_96,C_100] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2375,plain,(
    ! [C_434] :
      ( ~ r1_orders_2('#skF_5','#skF_9'(C_434),C_434)
      | ~ r1_lattice3('#skF_5','#skF_8',C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2379,plain,(
    ! [B_39] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_39))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_39),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_9'('#skF_3'('#skF_5',B_39)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_39)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_39)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_2375])).

tff(c_2399,plain,(
    ! [B_451] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_451))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_451),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_451,'#skF_9'('#skF_3'('#skF_5',B_451)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_451)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2379])).

tff(c_2402,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2372,c_2399])).

tff(c_2405,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2402])).

tff(c_2406,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2405])).

tff(c_2409,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2406])).

tff(c_2413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2409])).

tff(c_2415,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2405])).

tff(c_2384,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2414,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2405])).

tff(c_2416,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_2419,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2384,c_2416])).

tff(c_2422,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_2419])).

tff(c_2430,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2422])).

tff(c_2434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2430])).

tff(c_2435,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_2439,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2435])).

tff(c_2443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_2439])).

tff(c_2445,plain,(
    ! [D_455] :
      ( r1_orders_2('#skF_5',D_455,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_455)
      | ~ m1_subset_1(D_455,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2449,plain,(
    ! [B_39,C_58] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_39,C_58),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_39,C_58))
      | '#skF_2'('#skF_5',B_39,C_58) != C_58
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_2445])).

tff(c_2594,plain,(
    ! [B_485,C_486] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_485,C_486),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_485,C_486))
      | '#skF_2'('#skF_5',B_485,C_486) != C_486
      | r2_yellow_0('#skF_5',B_485)
      | ~ r1_lattice3('#skF_5',B_485,C_486)
      | ~ m1_subset_1(C_486,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2449])).

tff(c_2604,plain,(
    ! [B_485] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_485,'#skF_7'))
      | '#skF_2'('#skF_5',B_485,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_485)
      | ~ r1_lattice3('#skF_5',B_485,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2594,c_14])).

tff(c_2619,plain,(
    ! [B_487] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_487,'#skF_7'))
      | '#skF_2'('#skF_5',B_487,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_487)
      | ~ r1_lattice3('#skF_5',B_487,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_2604])).

tff(c_2629,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_2619])).

tff(c_2636,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_2629])).

tff(c_2637,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2636])).

tff(c_2532,plain,(
    ! [A_472,B_473,C_474] :
      ( m1_subset_1('#skF_1'(A_472,B_473,C_474),u1_struct_0(A_472))
      | r1_lattice3(A_472,B_473,'#skF_2'(A_472,B_473,C_474))
      | r2_yellow_0(A_472,B_473)
      | ~ r1_lattice3(A_472,B_473,C_474)
      | ~ m1_subset_1(C_474,u1_struct_0(A_472))
      | ~ l1_orders_2(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2444,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2536,plain,(
    ! [B_473,C_474] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_473,C_474),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_473,C_474))
      | r1_lattice3('#skF_5',B_473,'#skF_2'('#skF_5',B_473,C_474))
      | r2_yellow_0('#skF_5',B_473)
      | ~ r1_lattice3('#skF_5',B_473,C_474)
      | ~ m1_subset_1(C_474,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2532,c_2444])).

tff(c_2672,plain,(
    ! [B_499,C_500] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_499,C_500),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_499,C_500))
      | r1_lattice3('#skF_5',B_499,'#skF_2'('#skF_5',B_499,C_500))
      | r2_yellow_0('#skF_5',B_499)
      | ~ r1_lattice3('#skF_5',B_499,C_500)
      | ~ m1_subset_1(C_500,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2536])).

tff(c_2681,plain,(
    ! [B_499] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_499,'#skF_7'))
      | r1_lattice3('#skF_5',B_499,'#skF_2'('#skF_5',B_499,'#skF_7'))
      | r2_yellow_0('#skF_5',B_499)
      | ~ r1_lattice3('#skF_5',B_499,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2672,c_26])).

tff(c_2703,plain,(
    ! [B_501] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_501,'#skF_7'))
      | r1_lattice3('#skF_5',B_501,'#skF_2'('#skF_5',B_501,'#skF_7'))
      | r2_yellow_0('#skF_5',B_501)
      | ~ r1_lattice3('#skF_5',B_501,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_2681])).

tff(c_2707,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_2703])).

tff(c_2714,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_2707])).

tff(c_2715,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2714])).

tff(c_2515,plain,(
    ! [A_463,B_464,C_465] :
      ( r1_lattice3(A_463,B_464,'#skF_1'(A_463,B_464,C_465))
      | m1_subset_1('#skF_2'(A_463,B_464,C_465),u1_struct_0(A_463))
      | r2_yellow_0(A_463,B_464)
      | ~ r1_lattice3(A_463,B_464,C_465)
      | ~ m1_subset_1(C_465,u1_struct_0(A_463))
      | ~ l1_orders_2(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2519,plain,(
    ! [B_464,C_465] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_464,C_465),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_464,C_465))
      | r1_lattice3('#skF_5',B_464,'#skF_1'('#skF_5',B_464,C_465))
      | r2_yellow_0('#skF_5',B_464)
      | ~ r1_lattice3('#skF_5',B_464,C_465)
      | ~ m1_subset_1(C_465,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2515,c_2444])).

tff(c_2659,plain,(
    ! [B_495,C_496] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_495,C_496),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_495,C_496))
      | r1_lattice3('#skF_5',B_495,'#skF_1'('#skF_5',B_495,C_496))
      | r2_yellow_0('#skF_5',B_495)
      | ~ r1_lattice3('#skF_5',B_495,C_496)
      | ~ m1_subset_1(C_496,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2519])).

tff(c_2661,plain,(
    ! [B_495,C_496] :
      ( '#skF_2'('#skF_5',B_495,C_496) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_495,C_496))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_495,C_496),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_495,C_496))
      | r1_lattice3('#skF_5',B_495,'#skF_1'('#skF_5',B_495,C_496))
      | r2_yellow_0('#skF_5',B_495)
      | ~ r1_lattice3('#skF_5',B_495,C_496)
      | ~ m1_subset_1(C_496,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2659,c_38])).

tff(c_3160,plain,(
    ! [B_546,C_547] :
      ( '#skF_2'('#skF_5',B_546,C_547) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_546,C_547))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_546,C_547),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_546,C_547))
      | r1_lattice3('#skF_5',B_546,'#skF_1'('#skF_5',B_546,C_547))
      | r2_yellow_0('#skF_5',B_546)
      | ~ r1_lattice3('#skF_5',B_546,C_547)
      | ~ m1_subset_1(C_547,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_2661])).

tff(c_3167,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_3160])).

tff(c_3175,plain,(
    ! [B_548,C_549] :
      ( '#skF_2'('#skF_5',B_548,C_549) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_548,C_549))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_548,C_549))
      | r1_lattice3('#skF_5',B_548,'#skF_1'('#skF_5',B_548,C_549))
      | r2_yellow_0('#skF_5',B_548)
      | ~ r1_lattice3('#skF_5',B_548,C_549)
      | ~ m1_subset_1(C_549,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3167])).

tff(c_3181,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_3175])).

tff(c_3185,plain,(
    ! [B_550,C_551] :
      ( '#skF_2'('#skF_5',B_550,C_551) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_550,C_551))
      | r1_lattice3('#skF_5',B_550,'#skF_1'('#skF_5',B_550,C_551))
      | ~ r1_lattice3('#skF_5',B_550,'#skF_7')
      | r2_yellow_0('#skF_5',B_550)
      | ~ r1_lattice3('#skF_5',B_550,C_551)
      | ~ m1_subset_1(C_551,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_3181])).

tff(c_3187,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2715,c_3185])).

tff(c_3192,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2354,c_3187])).

tff(c_3193,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2637,c_3192])).

tff(c_2760,plain,(
    ! [A_506,B_507,C_508,E_509] :
      ( m1_subset_1('#skF_1'(A_506,B_507,C_508),u1_struct_0(A_506))
      | r1_orders_2(A_506,E_509,'#skF_2'(A_506,B_507,C_508))
      | ~ r1_lattice3(A_506,B_507,E_509)
      | ~ m1_subset_1(E_509,u1_struct_0(A_506))
      | r2_yellow_0(A_506,B_507)
      | ~ r1_lattice3(A_506,B_507,C_508)
      | ~ m1_subset_1(C_508,u1_struct_0(A_506))
      | ~ l1_orders_2(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2764,plain,(
    ! [B_507,C_508,E_509] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_507,C_508),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_507,C_508))
      | r1_orders_2('#skF_5',E_509,'#skF_2'('#skF_5',B_507,C_508))
      | ~ r1_lattice3('#skF_5',B_507,E_509)
      | ~ m1_subset_1(E_509,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_507)
      | ~ r1_lattice3('#skF_5',B_507,C_508)
      | ~ m1_subset_1(C_508,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2760,c_2444])).

tff(c_2835,plain,(
    ! [B_512,C_513,E_514] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_512,C_513),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_512,C_513))
      | r1_orders_2('#skF_5',E_514,'#skF_2'('#skF_5',B_512,C_513))
      | ~ r1_lattice3('#skF_5',B_512,E_514)
      | ~ m1_subset_1(E_514,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_512)
      | ~ r1_lattice3('#skF_5',B_512,C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2764])).

tff(c_2838,plain,(
    ! [E_64,B_512,E_514] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_512,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_512,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_512,'#skF_7'))
      | r1_orders_2('#skF_5',E_514,'#skF_2'('#skF_5',B_512,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_512,E_514)
      | ~ m1_subset_1(E_514,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_512)
      | ~ r1_lattice3('#skF_5',B_512,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2835,c_20])).

tff(c_2879,plain,(
    ! [E_64,B_512,E_514] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_512,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_512,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_512,'#skF_7'))
      | r1_orders_2('#skF_5',E_514,'#skF_2'('#skF_5',B_512,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_512,E_514)
      | ~ m1_subset_1(E_514,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_512)
      | ~ r1_lattice3('#skF_5',B_512,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_2838])).

tff(c_3405,plain,(
    ! [B_564,E_565] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_564,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_564,E_565)
      | ~ m1_subset_1(E_565,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_564)
      | ~ r1_lattice3('#skF_5',B_564,'#skF_7')
      | r1_orders_2('#skF_5',E_565,'#skF_2'('#skF_5',B_564,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2879])).

tff(c_2524,plain,(
    ! [A_469,B_470,C_471] :
      ( m1_subset_1('#skF_1'(A_469,B_470,C_471),u1_struct_0(A_469))
      | m1_subset_1('#skF_2'(A_469,B_470,C_471),u1_struct_0(A_469))
      | r2_yellow_0(A_469,B_470)
      | ~ r1_lattice3(A_469,B_470,C_471)
      | ~ m1_subset_1(C_471,u1_struct_0(A_469))
      | ~ l1_orders_2(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2528,plain,(
    ! [B_470,C_471] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_470,C_471),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_470,C_471))
      | m1_subset_1('#skF_2'('#skF_5',B_470,C_471),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_470)
      | ~ r1_lattice3('#skF_5',B_470,C_471)
      | ~ m1_subset_1(C_471,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2524,c_2444])).

tff(c_2531,plain,(
    ! [B_470,C_471] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_470,C_471),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_470,C_471))
      | m1_subset_1('#skF_2'('#skF_5',B_470,C_471),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_470)
      | ~ r1_lattice3('#skF_5',B_470,C_471)
      | ~ m1_subset_1(C_471,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2528])).

tff(c_2667,plain,(
    ! [B_497,C_498] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_497,C_498),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_497,C_498))
      | m1_subset_1('#skF_2'('#skF_5',B_497,C_498),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_497)
      | ~ r1_lattice3('#skF_5',B_497,C_498)
      | ~ m1_subset_1(C_498,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2528])).

tff(c_2804,plain,(
    ! [B_510,C_511] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_510,C_511),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_510,C_511))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_510,C_511),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_510,C_511))
      | r2_yellow_0('#skF_5',B_510)
      | ~ r1_lattice3('#skF_5',B_510,C_511)
      | ~ m1_subset_1(C_511,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2667,c_2444])).

tff(c_2810,plain,(
    ! [B_510] :
      ( m1_subset_1('#skF_2'('#skF_5',B_510,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_510,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_510,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_510,'#skF_7'))
      | r2_yellow_0('#skF_5',B_510)
      | ~ r1_lattice3('#skF_5',B_510,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2804,c_32])).

tff(c_2914,plain,(
    ! [B_515] :
      ( m1_subset_1('#skF_2'('#skF_5',B_515,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_515,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_515,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_515,'#skF_7'))
      | r2_yellow_0('#skF_5',B_515)
      | ~ r1_lattice3('#skF_5',B_515,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_2810])).

tff(c_2919,plain,(
    ! [B_516] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_516,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_516,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_516,'#skF_7'))
      | r2_yellow_0('#skF_5',B_516)
      | ~ r1_lattice3('#skF_5',B_516,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2914,c_2444])).

tff(c_2921,plain,(
    ! [B_516] :
      ( '#skF_2'('#skF_5',B_516,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_516,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_516,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_516,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_516,'#skF_7'))
      | r2_yellow_0('#skF_5',B_516)
      | ~ r1_lattice3('#skF_5',B_516,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2919,c_38])).

tff(c_2983,plain,(
    ! [B_522] :
      ( '#skF_2'('#skF_5',B_522,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_522,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_522,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_522,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_522,'#skF_7'))
      | r2_yellow_0('#skF_5',B_522)
      | ~ r1_lattice3('#skF_5',B_522,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_2921])).

tff(c_2990,plain,(
    ! [B_470] :
      ( '#skF_2'('#skF_5',B_470,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_470,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_470,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_470,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_470,'#skF_7'))
      | r2_yellow_0('#skF_5',B_470)
      | ~ r1_lattice3('#skF_5',B_470,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2531,c_2983])).

tff(c_3008,plain,(
    ! [B_526] :
      ( '#skF_2'('#skF_5',B_526,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_526,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_526,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_526,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_526,'#skF_7'))
      | r2_yellow_0('#skF_5',B_526)
      | ~ r1_lattice3('#skF_5',B_526,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2990])).

tff(c_3012,plain,(
    ! [B_526] :
      ( m1_subset_1('#skF_2'('#skF_5',B_526,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_526,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_526,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_526,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_526,'#skF_7'))
      | r2_yellow_0('#skF_5',B_526)
      | ~ r1_lattice3('#skF_5',B_526,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3008,c_32])).

tff(c_3069,plain,(
    ! [B_531] :
      ( m1_subset_1('#skF_2'('#skF_5',B_531,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_531,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_531,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_531,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_531,'#skF_7'))
      | r2_yellow_0('#skF_5',B_531)
      | ~ r1_lattice3('#skF_5',B_531,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_3012])).

tff(c_2924,plain,(
    ! [B_516] :
      ( '#skF_2'('#skF_5',B_516,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_516,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_516,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_516,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_516,'#skF_7'))
      | r2_yellow_0('#skF_5',B_516)
      | ~ r1_lattice3('#skF_5',B_516,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_2921])).

tff(c_3076,plain,(
    ! [B_531] :
      ( '#skF_2'('#skF_5',B_531,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_531,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_531,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_531,'#skF_7'))
      | r2_yellow_0('#skF_5',B_531)
      | ~ r1_lattice3('#skF_5',B_531,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3069,c_2924])).

tff(c_3412,plain,(
    ! [B_564] :
      ( '#skF_2'('#skF_5',B_564,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_564,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_564,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_564)
      | ~ r1_lattice3('#skF_5',B_564,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3405,c_3076])).

tff(c_3467,plain,(
    ! [B_566] :
      ( '#skF_2'('#skF_5',B_566,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_566,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_566,'#skF_7'))
      | r2_yellow_0('#skF_5',B_566)
      | ~ r1_lattice3('#skF_5',B_566,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_3412])).

tff(c_3470,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_3193,c_3467])).

tff(c_3487,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_2715,c_3470])).

tff(c_3489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_2637,c_3487])).

tff(c_3490,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3529,plain,(
    ! [B_571,C_572] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_571,C_572),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_571,C_572))
      | '#skF_2'('#skF_5',B_571,C_572) != C_572
      | r2_yellow_0('#skF_5',B_571)
      | ~ r1_lattice3('#skF_5',B_571,C_572)
      | ~ m1_subset_1(C_572,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3525,c_3490])).

tff(c_3614,plain,(
    ! [B_597,C_598] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_597,C_598),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_597,C_598))
      | '#skF_2'('#skF_5',B_597,C_598) != C_598
      | r2_yellow_0('#skF_5',B_597)
      | ~ r1_lattice3('#skF_5',B_597,C_598)
      | ~ m1_subset_1(C_598,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3529])).

tff(c_3621,plain,(
    ! [B_597] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_597,'#skF_7'))
      | '#skF_2'('#skF_5',B_597,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_597)
      | ~ r1_lattice3('#skF_5',B_597,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3614,c_14])).

tff(c_3633,plain,(
    ! [B_599] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_599,'#skF_7'))
      | '#skF_2'('#skF_5',B_599,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_599)
      | ~ r1_lattice3('#skF_5',B_599,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_3621])).

tff(c_3643,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_3633])).

tff(c_3650,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_3643])).

tff(c_3651,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3650])).

tff(c_3597,plain,(
    ! [A_588,B_589,C_590] :
      ( m1_subset_1('#skF_1'(A_588,B_589,C_590),u1_struct_0(A_588))
      | r1_lattice3(A_588,B_589,'#skF_2'(A_588,B_589,C_590))
      | r2_yellow_0(A_588,B_589)
      | ~ r1_lattice3(A_588,B_589,C_590)
      | ~ m1_subset_1(C_590,u1_struct_0(A_588))
      | ~ l1_orders_2(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3601,plain,(
    ! [B_589,C_590] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_589,C_590),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_589,C_590))
      | r1_lattice3('#skF_5',B_589,'#skF_2'('#skF_5',B_589,C_590))
      | r2_yellow_0('#skF_5',B_589)
      | ~ r1_lattice3('#skF_5',B_589,C_590)
      | ~ m1_subset_1(C_590,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3597,c_3490])).

tff(c_3684,plain,(
    ! [B_610,C_611] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_610,C_611),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_610,C_611))
      | r1_lattice3('#skF_5',B_610,'#skF_2'('#skF_5',B_610,C_611))
      | r2_yellow_0('#skF_5',B_610)
      | ~ r1_lattice3('#skF_5',B_610,C_611)
      | ~ m1_subset_1(C_611,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3601])).

tff(c_3690,plain,(
    ! [B_610] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_610,'#skF_7'))
      | r1_lattice3('#skF_5',B_610,'#skF_2'('#skF_5',B_610,'#skF_7'))
      | r2_yellow_0('#skF_5',B_610)
      | ~ r1_lattice3('#skF_5',B_610,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3684,c_26])).

tff(c_3715,plain,(
    ! [B_612] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_612,'#skF_7'))
      | r1_lattice3('#skF_5',B_612,'#skF_2'('#skF_5',B_612,'#skF_7'))
      | r2_yellow_0('#skF_5',B_612)
      | ~ r1_lattice3('#skF_5',B_612,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_3690])).

tff(c_3718,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_3715])).

tff(c_3725,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_3718])).

tff(c_3726,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3725])).

tff(c_3589,plain,(
    ! [A_585,B_586,C_587] :
      ( r1_lattice3(A_585,B_586,'#skF_1'(A_585,B_586,C_587))
      | m1_subset_1('#skF_2'(A_585,B_586,C_587),u1_struct_0(A_585))
      | r2_yellow_0(A_585,B_586)
      | ~ r1_lattice3(A_585,B_586,C_587)
      | ~ m1_subset_1(C_587,u1_struct_0(A_585))
      | ~ l1_orders_2(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3593,plain,(
    ! [B_586,C_587] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_586,C_587),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_586,C_587))
      | r1_lattice3('#skF_5',B_586,'#skF_1'('#skF_5',B_586,C_587))
      | r2_yellow_0('#skF_5',B_586)
      | ~ r1_lattice3('#skF_5',B_586,C_587)
      | ~ m1_subset_1(C_587,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3589,c_3490])).

tff(c_3731,plain,(
    ! [B_613,C_614] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_613,C_614),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_613,C_614))
      | r1_lattice3('#skF_5',B_613,'#skF_1'('#skF_5',B_613,C_614))
      | r2_yellow_0('#skF_5',B_613)
      | ~ r1_lattice3('#skF_5',B_613,C_614)
      | ~ m1_subset_1(C_614,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3593])).

tff(c_3733,plain,(
    ! [B_613,C_614] :
      ( '#skF_2'('#skF_5',B_613,C_614) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_613,C_614))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_613,C_614),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_613,C_614))
      | r1_lattice3('#skF_5',B_613,'#skF_1'('#skF_5',B_613,C_614))
      | r2_yellow_0('#skF_5',B_613)
      | ~ r1_lattice3('#skF_5',B_613,C_614)
      | ~ m1_subset_1(C_614,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3731,c_38])).

tff(c_4503,plain,(
    ! [B_676,C_677] :
      ( '#skF_2'('#skF_5',B_676,C_677) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_676,C_677))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_676,C_677),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_676,C_677))
      | r1_lattice3('#skF_5',B_676,'#skF_1'('#skF_5',B_676,C_677))
      | r2_yellow_0('#skF_5',B_676)
      | ~ r1_lattice3('#skF_5',B_676,C_677)
      | ~ m1_subset_1(C_677,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_3733])).

tff(c_4508,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_4503])).

tff(c_4513,plain,(
    ! [B_678,C_679] :
      ( '#skF_2'('#skF_5',B_678,C_679) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_678,C_679))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_678,C_679))
      | r1_lattice3('#skF_5',B_678,'#skF_1'('#skF_5',B_678,C_679))
      | r2_yellow_0('#skF_5',B_678)
      | ~ r1_lattice3('#skF_5',B_678,C_679)
      | ~ m1_subset_1(C_679,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4508])).

tff(c_4521,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_4513])).

tff(c_4528,plain,(
    ! [B_680,C_681] :
      ( '#skF_2'('#skF_5',B_680,C_681) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_680,C_681))
      | r1_lattice3('#skF_5',B_680,'#skF_1'('#skF_5',B_680,C_681))
      | ~ r1_lattice3('#skF_5',B_680,'#skF_7')
      | r2_yellow_0('#skF_5',B_680)
      | ~ r1_lattice3('#skF_5',B_680,C_681)
      | ~ m1_subset_1(C_681,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_4521])).

tff(c_4530,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3726,c_4528])).

tff(c_4535,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2354,c_4530])).

tff(c_4536,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3651,c_4535])).

tff(c_3778,plain,(
    ! [A_621,B_622,C_623,E_624] :
      ( m1_subset_1('#skF_1'(A_621,B_622,C_623),u1_struct_0(A_621))
      | r1_orders_2(A_621,E_624,'#skF_2'(A_621,B_622,C_623))
      | ~ r1_lattice3(A_621,B_622,E_624)
      | ~ m1_subset_1(E_624,u1_struct_0(A_621))
      | r2_yellow_0(A_621,B_622)
      | ~ r1_lattice3(A_621,B_622,C_623)
      | ~ m1_subset_1(C_623,u1_struct_0(A_621))
      | ~ l1_orders_2(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3782,plain,(
    ! [B_622,C_623,E_624] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_622,C_623),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_622,C_623))
      | r1_orders_2('#skF_5',E_624,'#skF_2'('#skF_5',B_622,C_623))
      | ~ r1_lattice3('#skF_5',B_622,E_624)
      | ~ m1_subset_1(E_624,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_622)
      | ~ r1_lattice3('#skF_5',B_622,C_623)
      | ~ m1_subset_1(C_623,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3778,c_3490])).

tff(c_3815,plain,(
    ! [B_625,C_626,E_627] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_625,C_626),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_625,C_626))
      | r1_orders_2('#skF_5',E_627,'#skF_2'('#skF_5',B_625,C_626))
      | ~ r1_lattice3('#skF_5',B_625,E_627)
      | ~ m1_subset_1(E_627,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_625)
      | ~ r1_lattice3('#skF_5',B_625,C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3782])).

tff(c_3818,plain,(
    ! [E_64,B_625,E_627] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_625,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_625,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_625,'#skF_7'))
      | r1_orders_2('#skF_5',E_627,'#skF_2'('#skF_5',B_625,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_625,E_627)
      | ~ m1_subset_1(E_627,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_625)
      | ~ r1_lattice3('#skF_5',B_625,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3815,c_20])).

tff(c_3855,plain,(
    ! [E_64,B_625,E_627] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_625,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_625,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_625,'#skF_7'))
      | r1_orders_2('#skF_5',E_627,'#skF_2'('#skF_5',B_625,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_625,E_627)
      | ~ m1_subset_1(E_627,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_625)
      | ~ r1_lattice3('#skF_5',B_625,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_3818])).

tff(c_4342,plain,(
    ! [B_664,E_665] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_664,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_664,E_665)
      | ~ m1_subset_1(E_665,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_664)
      | ~ r1_lattice3('#skF_5',B_664,'#skF_7')
      | r1_orders_2('#skF_5',E_665,'#skF_2'('#skF_5',B_664,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3855])).

tff(c_3606,plain,(
    ! [A_594,B_595,C_596] :
      ( m1_subset_1('#skF_1'(A_594,B_595,C_596),u1_struct_0(A_594))
      | m1_subset_1('#skF_2'(A_594,B_595,C_596),u1_struct_0(A_594))
      | r2_yellow_0(A_594,B_595)
      | ~ r1_lattice3(A_594,B_595,C_596)
      | ~ m1_subset_1(C_596,u1_struct_0(A_594))
      | ~ l1_orders_2(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3610,plain,(
    ! [B_595,C_596] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_595,C_596),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_595,C_596))
      | m1_subset_1('#skF_2'('#skF_5',B_595,C_596),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_595)
      | ~ r1_lattice3('#skF_5',B_595,C_596)
      | ~ m1_subset_1(C_596,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3606,c_3490])).

tff(c_3613,plain,(
    ! [B_595,C_596] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_595,C_596),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_595,C_596))
      | m1_subset_1('#skF_2'('#skF_5',B_595,C_596),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_595)
      | ~ r1_lattice3('#skF_5',B_595,C_596)
      | ~ m1_subset_1(C_596,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3610])).

tff(c_3740,plain,(
    ! [B_615,C_616] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_615,C_616),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_615,C_616))
      | m1_subset_1('#skF_2'('#skF_5',B_615,C_616),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_615)
      | ~ r1_lattice3('#skF_5',B_615,C_616)
      | ~ m1_subset_1(C_616,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3610])).

tff(c_3937,plain,(
    ! [B_630,C_631] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_630,C_631),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_630,C_631))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_630,C_631),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_630,C_631))
      | r2_yellow_0('#skF_5',B_630)
      | ~ r1_lattice3('#skF_5',B_630,C_631)
      | ~ m1_subset_1(C_631,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3740,c_3490])).

tff(c_3946,plain,(
    ! [B_630] :
      ( m1_subset_1('#skF_2'('#skF_5',B_630,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_630,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_630,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_630,'#skF_7'))
      | r2_yellow_0('#skF_5',B_630)
      | ~ r1_lattice3('#skF_5',B_630,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3937,c_32])).

tff(c_4017,plain,(
    ! [B_634] :
      ( m1_subset_1('#skF_2'('#skF_5',B_634,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_634,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_634,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_634,'#skF_7'))
      | r2_yellow_0('#skF_5',B_634)
      | ~ r1_lattice3('#skF_5',B_634,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_3946])).

tff(c_4022,plain,(
    ! [B_635] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_635,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_635,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_635,'#skF_7'))
      | r2_yellow_0('#skF_5',B_635)
      | ~ r1_lattice3('#skF_5',B_635,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4017,c_3490])).

tff(c_4024,plain,(
    ! [B_635] :
      ( '#skF_2'('#skF_5',B_635,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_635,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_635,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_635,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_635,'#skF_7'))
      | r2_yellow_0('#skF_5',B_635)
      | ~ r1_lattice3('#skF_5',B_635,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4022,c_38])).

tff(c_4033,plain,(
    ! [B_639] :
      ( '#skF_2'('#skF_5',B_639,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_639,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_639,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_639,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_639,'#skF_7'))
      | r2_yellow_0('#skF_5',B_639)
      | ~ r1_lattice3('#skF_5',B_639,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4024])).

tff(c_4040,plain,(
    ! [B_595] :
      ( '#skF_2'('#skF_5',B_595,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_595,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_595,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_595,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_595,'#skF_7'))
      | r2_yellow_0('#skF_5',B_595)
      | ~ r1_lattice3('#skF_5',B_595,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3613,c_4033])).

tff(c_4052,plain,(
    ! [B_640] :
      ( '#skF_2'('#skF_5',B_640,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_640,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_640,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_640,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_640,'#skF_7'))
      | r2_yellow_0('#skF_5',B_640)
      | ~ r1_lattice3('#skF_5',B_640,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4040])).

tff(c_4058,plain,(
    ! [B_640] :
      ( m1_subset_1('#skF_2'('#skF_5',B_640,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_640,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_640,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_640,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_640,'#skF_7'))
      | r2_yellow_0('#skF_5',B_640)
      | ~ r1_lattice3('#skF_5',B_640,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4052,c_32])).

tff(c_4113,plain,(
    ! [B_646] :
      ( m1_subset_1('#skF_2'('#skF_5',B_646,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_646,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_646,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_646,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_646,'#skF_7'))
      | r2_yellow_0('#skF_5',B_646)
      | ~ r1_lattice3('#skF_5',B_646,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_4058])).

tff(c_4027,plain,(
    ! [B_635] :
      ( '#skF_2'('#skF_5',B_635,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_635,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_635,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_635,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_635,'#skF_7'))
      | r2_yellow_0('#skF_5',B_635)
      | ~ r1_lattice3('#skF_5',B_635,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4024])).

tff(c_4120,plain,(
    ! [B_646] :
      ( '#skF_2'('#skF_5',B_646,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_646,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_646,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_646,'#skF_7'))
      | r2_yellow_0('#skF_5',B_646)
      | ~ r1_lattice3('#skF_5',B_646,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4113,c_4027])).

tff(c_4346,plain,(
    ! [B_664] :
      ( '#skF_2'('#skF_5',B_664,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_664,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_664,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_664)
      | ~ r1_lattice3('#skF_5',B_664,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4342,c_4120])).

tff(c_4371,plain,(
    ! [B_664] :
      ( '#skF_2'('#skF_5',B_664,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_664,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_664,'#skF_7'))
      | r2_yellow_0('#skF_5',B_664)
      | ~ r1_lattice3('#skF_5',B_664,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4346])).

tff(c_4539,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_4536,c_4371])).

tff(c_4547,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_3726,c_4539])).

tff(c_4549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3651,c_4547])).

tff(c_4550,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4576,plain,(
    ! [B_684,C_685] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_684,C_685),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_684,C_685))
      | '#skF_2'('#skF_5',B_684,C_685) != C_685
      | r2_yellow_0('#skF_5',B_684)
      | ~ r1_lattice3('#skF_5',B_684,C_685)
      | ~ m1_subset_1(C_685,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4572,c_4550])).

tff(c_4678,plain,(
    ! [B_714,C_715] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_714,C_715),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_714,C_715))
      | '#skF_2'('#skF_5',B_714,C_715) != C_715
      | r2_yellow_0('#skF_5',B_714)
      | ~ r1_lattice3('#skF_5',B_714,C_715)
      | ~ m1_subset_1(C_715,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4576])).

tff(c_4688,plain,(
    ! [B_714] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_714,'#skF_7'))
      | '#skF_2'('#skF_5',B_714,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_714)
      | ~ r1_lattice3('#skF_5',B_714,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4678,c_14])).

tff(c_4703,plain,(
    ! [B_716] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_716,'#skF_7'))
      | '#skF_2'('#skF_5',B_716,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_716)
      | ~ r1_lattice3('#skF_5',B_716,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_4688])).

tff(c_4713,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_4703])).

tff(c_4720,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_4713])).

tff(c_4721,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4720])).

tff(c_4622,plain,(
    ! [A_693,B_694,C_695] :
      ( m1_subset_1('#skF_1'(A_693,B_694,C_695),u1_struct_0(A_693))
      | r1_lattice3(A_693,B_694,'#skF_2'(A_693,B_694,C_695))
      | r2_yellow_0(A_693,B_694)
      | ~ r1_lattice3(A_693,B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0(A_693))
      | ~ l1_orders_2(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4626,plain,(
    ! [B_694,C_695] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_694,C_695),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_694,C_695))
      | r1_lattice3('#skF_5',B_694,'#skF_2'('#skF_5',B_694,C_695))
      | r2_yellow_0('#skF_5',B_694)
      | ~ r1_lattice3('#skF_5',B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4622,c_4550])).

tff(c_4770,plain,(
    ! [B_726,C_727] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_726,C_727),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_726,C_727))
      | r1_lattice3('#skF_5',B_726,'#skF_2'('#skF_5',B_726,C_727))
      | r2_yellow_0('#skF_5',B_726)
      | ~ r1_lattice3('#skF_5',B_726,C_727)
      | ~ m1_subset_1(C_727,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4626])).

tff(c_4776,plain,(
    ! [B_726] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_726,'#skF_7'))
      | r1_lattice3('#skF_5',B_726,'#skF_2'('#skF_5',B_726,'#skF_7'))
      | r2_yellow_0('#skF_5',B_726)
      | ~ r1_lattice3('#skF_5',B_726,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4770,c_26])).

tff(c_4795,plain,(
    ! [B_728] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_728,'#skF_7'))
      | r1_lattice3('#skF_5',B_728,'#skF_2'('#skF_5',B_728,'#skF_7'))
      | r2_yellow_0('#skF_5',B_728)
      | ~ r1_lattice3('#skF_5',B_728,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_4776])).

tff(c_4798,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_4795])).

tff(c_4805,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_2354,c_4798])).

tff(c_4806,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4805])).

tff(c_4635,plain,(
    ! [A_699,B_700,C_701] :
      ( r1_lattice3(A_699,B_700,'#skF_1'(A_699,B_700,C_701))
      | m1_subset_1('#skF_2'(A_699,B_700,C_701),u1_struct_0(A_699))
      | r2_yellow_0(A_699,B_700)
      | ~ r1_lattice3(A_699,B_700,C_701)
      | ~ m1_subset_1(C_701,u1_struct_0(A_699))
      | ~ l1_orders_2(A_699) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4639,plain,(
    ! [B_700,C_701] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_700,C_701),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_700,C_701))
      | r1_lattice3('#skF_5',B_700,'#skF_1'('#skF_5',B_700,C_701))
      | r2_yellow_0('#skF_5',B_700)
      | ~ r1_lattice3('#skF_5',B_700,C_701)
      | ~ m1_subset_1(C_701,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4635,c_4550])).

tff(c_4840,plain,(
    ! [B_733,C_734] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_733,C_734),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_733,C_734))
      | r1_lattice3('#skF_5',B_733,'#skF_1'('#skF_5',B_733,C_734))
      | r2_yellow_0('#skF_5',B_733)
      | ~ r1_lattice3('#skF_5',B_733,C_734)
      | ~ m1_subset_1(C_734,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4639])).

tff(c_4842,plain,(
    ! [B_733,C_734] :
      ( '#skF_2'('#skF_5',B_733,C_734) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_733,C_734))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_733,C_734),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_733,C_734))
      | r1_lattice3('#skF_5',B_733,'#skF_1'('#skF_5',B_733,C_734))
      | r2_yellow_0('#skF_5',B_733)
      | ~ r1_lattice3('#skF_5',B_733,C_734)
      | ~ m1_subset_1(C_734,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4840,c_38])).

tff(c_5530,plain,(
    ! [B_791,C_792] :
      ( '#skF_2'('#skF_5',B_791,C_792) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_791,C_792))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_791,C_792),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_791,C_792))
      | r1_lattice3('#skF_5',B_791,'#skF_1'('#skF_5',B_791,C_792))
      | r2_yellow_0('#skF_5',B_791)
      | ~ r1_lattice3('#skF_5',B_791,C_792)
      | ~ m1_subset_1(C_792,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4842])).

tff(c_5535,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_5530])).

tff(c_5540,plain,(
    ! [B_793,C_794] :
      ( '#skF_2'('#skF_5',B_793,C_794) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_793,C_794))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_793,C_794))
      | r1_lattice3('#skF_5',B_793,'#skF_1'('#skF_5',B_793,C_794))
      | r2_yellow_0('#skF_5',B_793)
      | ~ r1_lattice3('#skF_5',B_793,C_794)
      | ~ m1_subset_1(C_794,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5535])).

tff(c_5547,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_5540])).

tff(c_5555,plain,(
    ! [B_795,C_796] :
      ( '#skF_2'('#skF_5',B_795,C_796) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_795,C_796))
      | r1_lattice3('#skF_5',B_795,'#skF_1'('#skF_5',B_795,C_796))
      | ~ r1_lattice3('#skF_5',B_795,'#skF_7')
      | r2_yellow_0('#skF_5',B_795)
      | ~ r1_lattice3('#skF_5',B_795,C_796)
      | ~ m1_subset_1(C_796,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_5547])).

tff(c_5557,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4806,c_5555])).

tff(c_5562,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2354,c_5557])).

tff(c_5563,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4721,c_5562])).

tff(c_4722,plain,(
    ! [A_717,B_718,C_719,E_720] :
      ( m1_subset_1('#skF_1'(A_717,B_718,C_719),u1_struct_0(A_717))
      | r1_orders_2(A_717,E_720,'#skF_2'(A_717,B_718,C_719))
      | ~ r1_lattice3(A_717,B_718,E_720)
      | ~ m1_subset_1(E_720,u1_struct_0(A_717))
      | r2_yellow_0(A_717,B_718)
      | ~ r1_lattice3(A_717,B_718,C_719)
      | ~ m1_subset_1(C_719,u1_struct_0(A_717))
      | ~ l1_orders_2(A_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4726,plain,(
    ! [B_718,C_719,E_720] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_718,C_719),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_718,C_719))
      | r1_orders_2('#skF_5',E_720,'#skF_2'('#skF_5',B_718,C_719))
      | ~ r1_lattice3('#skF_5',B_718,E_720)
      | ~ m1_subset_1(E_720,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_718)
      | ~ r1_lattice3('#skF_5',B_718,C_719)
      | ~ m1_subset_1(C_719,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4722,c_4550])).

tff(c_4905,plain,(
    ! [B_741,C_742,E_743] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_741,C_742),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_741,C_742))
      | r1_orders_2('#skF_5',E_743,'#skF_2'('#skF_5',B_741,C_742))
      | ~ r1_lattice3('#skF_5',B_741,E_743)
      | ~ m1_subset_1(E_743,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_741)
      | ~ r1_lattice3('#skF_5',B_741,C_742)
      | ~ m1_subset_1(C_742,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4726])).

tff(c_4908,plain,(
    ! [E_64,B_741,E_743] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_741,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_741,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_741,'#skF_7'))
      | r1_orders_2('#skF_5',E_743,'#skF_2'('#skF_5',B_741,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_741,E_743)
      | ~ m1_subset_1(E_743,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_741)
      | ~ r1_lattice3('#skF_5',B_741,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4905,c_20])).

tff(c_4945,plain,(
    ! [E_64,B_741,E_743] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_741,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_741,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_741,'#skF_7'))
      | r1_orders_2('#skF_5',E_743,'#skF_2'('#skF_5',B_741,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_741,E_743)
      | ~ m1_subset_1(E_743,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_741)
      | ~ r1_lattice3('#skF_5',B_741,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_4908])).

tff(c_5378,plain,(
    ! [B_780,E_781] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_780,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_780,E_781)
      | ~ m1_subset_1(E_781,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_780)
      | ~ r1_lattice3('#skF_5',B_780,'#skF_7')
      | r1_orders_2('#skF_5',E_781,'#skF_2'('#skF_5',B_780,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4945])).

tff(c_4644,plain,(
    ! [A_705,B_706,C_707] :
      ( m1_subset_1('#skF_1'(A_705,B_706,C_707),u1_struct_0(A_705))
      | m1_subset_1('#skF_2'(A_705,B_706,C_707),u1_struct_0(A_705))
      | r2_yellow_0(A_705,B_706)
      | ~ r1_lattice3(A_705,B_706,C_707)
      | ~ m1_subset_1(C_707,u1_struct_0(A_705))
      | ~ l1_orders_2(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4648,plain,(
    ! [B_706,C_707] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_706,C_707),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_706,C_707))
      | m1_subset_1('#skF_2'('#skF_5',B_706,C_707),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_706)
      | ~ r1_lattice3('#skF_5',B_706,C_707)
      | ~ m1_subset_1(C_707,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4644,c_4550])).

tff(c_4651,plain,(
    ! [B_706,C_707] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_706,C_707),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_706,C_707))
      | m1_subset_1('#skF_2'('#skF_5',B_706,C_707),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_706)
      | ~ r1_lattice3('#skF_5',B_706,C_707)
      | ~ m1_subset_1(C_707,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4648])).

tff(c_4751,plain,(
    ! [B_721,C_722] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_721,C_722),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_721,C_722))
      | m1_subset_1('#skF_2'('#skF_5',B_721,C_722),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_721)
      | ~ r1_lattice3('#skF_5',B_721,C_722)
      | ~ m1_subset_1(C_722,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4648])).

tff(c_4874,plain,(
    ! [B_739,C_740] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_739,C_740),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_739,C_740))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_739,C_740),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_739,C_740))
      | r2_yellow_0('#skF_5',B_739)
      | ~ r1_lattice3('#skF_5',B_739,C_740)
      | ~ m1_subset_1(C_740,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4751,c_4550])).

tff(c_4880,plain,(
    ! [B_739] :
      ( m1_subset_1('#skF_2'('#skF_5',B_739,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_739,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_739,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_739,'#skF_7'))
      | r2_yellow_0('#skF_5',B_739)
      | ~ r1_lattice3('#skF_5',B_739,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4874,c_32])).

tff(c_4979,plain,(
    ! [B_744] :
      ( m1_subset_1('#skF_2'('#skF_5',B_744,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_744,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_744,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_744,'#skF_7'))
      | r2_yellow_0('#skF_5',B_744)
      | ~ r1_lattice3('#skF_5',B_744,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_40,c_4880])).

tff(c_4984,plain,(
    ! [B_745] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_745,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_745,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_745,'#skF_7'))
      | r2_yellow_0('#skF_5',B_745)
      | ~ r1_lattice3('#skF_5',B_745,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4979,c_4550])).

tff(c_4986,plain,(
    ! [B_745] :
      ( '#skF_2'('#skF_5',B_745,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_745,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_745,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_745,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_745,'#skF_7'))
      | r2_yellow_0('#skF_5',B_745)
      | ~ r1_lattice3('#skF_5',B_745,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4984,c_38])).

tff(c_5043,plain,(
    ! [B_751] :
      ( '#skF_2'('#skF_5',B_751,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_751,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_751,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_751,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_751,'#skF_7'))
      | r2_yellow_0('#skF_5',B_751)
      | ~ r1_lattice3('#skF_5',B_751,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4986])).

tff(c_5050,plain,(
    ! [B_706] :
      ( '#skF_2'('#skF_5',B_706,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_706,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_706,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_706,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_706,'#skF_7'))
      | r2_yellow_0('#skF_5',B_706)
      | ~ r1_lattice3('#skF_5',B_706,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4651,c_5043])).

tff(c_5068,plain,(
    ! [B_755] :
      ( '#skF_2'('#skF_5',B_755,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_755,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_755,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_755,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_755,'#skF_7'))
      | r2_yellow_0('#skF_5',B_755)
      | ~ r1_lattice3('#skF_5',B_755,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_5050])).

tff(c_5072,plain,(
    ! [B_755] :
      ( m1_subset_1('#skF_2'('#skF_5',B_755,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_755,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_755,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_755,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_755,'#skF_7'))
      | r2_yellow_0('#skF_5',B_755)
      | ~ r1_lattice3('#skF_5',B_755,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5068,c_32])).

tff(c_5123,plain,(
    ! [B_758] :
      ( m1_subset_1('#skF_2'('#skF_5',B_758,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_758,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_758,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_758,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_758,'#skF_7'))
      | r2_yellow_0('#skF_5',B_758)
      | ~ r1_lattice3('#skF_5',B_758,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_5072])).

tff(c_4989,plain,(
    ! [B_745] :
      ( '#skF_2'('#skF_5',B_745,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_745,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_745,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_745,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_745,'#skF_7'))
      | r2_yellow_0('#skF_5',B_745)
      | ~ r1_lattice3('#skF_5',B_745,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81,c_4986])).

tff(c_5130,plain,(
    ! [B_758] :
      ( '#skF_2'('#skF_5',B_758,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_758,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_758,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_758,'#skF_7'))
      | r2_yellow_0('#skF_5',B_758)
      | ~ r1_lattice3('#skF_5',B_758,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5123,c_4989])).

tff(c_5382,plain,(
    ! [B_780] :
      ( '#skF_2'('#skF_5',B_780,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_780,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_780,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_780)
      | ~ r1_lattice3('#skF_5',B_780,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5378,c_5130])).

tff(c_5407,plain,(
    ! [B_780] :
      ( '#skF_2'('#skF_5',B_780,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_780,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_780,'#skF_7'))
      | r2_yellow_0('#skF_5',B_780)
      | ~ r1_lattice3('#skF_5',B_780,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_5382])).

tff(c_5566,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_5563,c_5407])).

tff(c_5574,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2354,c_4806,c_5566])).

tff(c_5576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4721,c_5574])).

tff(c_5577,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5671,plain,(
    ! [A_844,D_845,B_846] :
      ( r1_orders_2(A_844,D_845,'#skF_3'(A_844,B_846))
      | ~ r1_lattice3(A_844,B_846,D_845)
      | ~ m1_subset_1(D_845,u1_struct_0(A_844))
      | ~ r2_yellow_0(A_844,B_846)
      | ~ l1_orders_2(A_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5578,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_50,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5668,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5578,c_50])).

tff(c_5675,plain,(
    ! [B_846] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_846))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_846),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_846,'#skF_9'('#skF_3'('#skF_5',B_846)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_846)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_846)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5671,c_5668])).

tff(c_5713,plain,(
    ! [B_886] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_886))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_886),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_886,'#skF_9'('#skF_3'('#skF_5',B_886)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_886)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_886) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5675])).

tff(c_5716,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5577,c_5713])).

tff(c_5719,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5716])).

tff(c_5720,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5719])).

tff(c_5723,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_5720])).

tff(c_5727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5723])).

tff(c_5729,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5719])).

tff(c_66,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5580,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5578,c_66])).

tff(c_5728,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5719])).

tff(c_5730,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5728])).

tff(c_5733,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5580,c_5730])).

tff(c_5736,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5729,c_5733])).

tff(c_5739,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5736])).

tff(c_5743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5739])).

tff(c_5744,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5728])).

tff(c_5777,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_5744])).

tff(c_5781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76,c_5777])).

tff(c_5783,plain,(
    ~ r2_yellow_0('#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_74,plain,
    ( m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | r2_yellow_0('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5784,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5783,c_74])).

tff(c_5782,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_5840,plain,(
    ! [A_912,B_913,C_914] :
      ( m1_subset_1('#skF_1'(A_912,B_913,C_914),u1_struct_0(A_912))
      | '#skF_2'(A_912,B_913,C_914) != C_914
      | r2_yellow_0(A_912,B_913)
      | ~ r1_lattice3(A_912,B_913,C_914)
      | ~ m1_subset_1(C_914,u1_struct_0(A_912))
      | ~ l1_orders_2(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5787,plain,(
    ! [D_96] :
      ( r1_orders_2('#skF_5',D_96,'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6',D_96)
      | ~ m1_subset_1(D_96,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5783,c_70])).

tff(c_5844,plain,(
    ! [B_913,C_914] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_913,C_914),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_913,C_914))
      | '#skF_2'('#skF_5',B_913,C_914) != C_914
      | r2_yellow_0('#skF_5',B_913)
      | ~ r1_lattice3('#skF_5',B_913,C_914)
      | ~ m1_subset_1(C_914,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5840,c_5787])).

tff(c_5935,plain,(
    ! [B_945,C_946] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_945,C_946),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_945,C_946))
      | '#skF_2'('#skF_5',B_945,C_946) != C_946
      | r2_yellow_0('#skF_5',B_945)
      | ~ r1_lattice3('#skF_5',B_945,C_946)
      | ~ m1_subset_1(C_946,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5844])).

tff(c_5945,plain,(
    ! [B_945] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_945,'#skF_7'))
      | '#skF_2'('#skF_5',B_945,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_945)
      | ~ r1_lattice3('#skF_5',B_945,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5935,c_14])).

tff(c_5960,plain,(
    ! [B_947] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_947,'#skF_7'))
      | '#skF_2'('#skF_5',B_947,'#skF_7') != '#skF_7'
      | r2_yellow_0('#skF_5',B_947)
      | ~ r1_lattice3('#skF_5',B_947,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_40,c_5945])).

tff(c_5970,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_5960])).

tff(c_5977,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5784,c_5782,c_5970])).

tff(c_5978,plain,(
    '#skF_2'('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5977])).

tff(c_5913,plain,(
    ! [A_933,B_934,C_935] :
      ( m1_subset_1('#skF_1'(A_933,B_934,C_935),u1_struct_0(A_933))
      | r1_lattice3(A_933,B_934,'#skF_2'(A_933,B_934,C_935))
      | r2_yellow_0(A_933,B_934)
      | ~ r1_lattice3(A_933,B_934,C_935)
      | ~ m1_subset_1(C_935,u1_struct_0(A_933))
      | ~ l1_orders_2(A_933) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5917,plain,(
    ! [B_934,C_935] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_934,C_935),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_934,C_935))
      | r1_lattice3('#skF_5',B_934,'#skF_2'('#skF_5',B_934,C_935))
      | r2_yellow_0('#skF_5',B_934)
      | ~ r1_lattice3('#skF_5',B_934,C_935)
      | ~ m1_subset_1(C_935,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5913,c_5787])).

tff(c_6030,plain,(
    ! [B_959,C_960] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_959,C_960),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_959,C_960))
      | r1_lattice3('#skF_5',B_959,'#skF_2'('#skF_5',B_959,C_960))
      | r2_yellow_0('#skF_5',B_959)
      | ~ r1_lattice3('#skF_5',B_959,C_960)
      | ~ m1_subset_1(C_960,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5917])).

tff(c_6033,plain,(
    ! [B_959] :
      ( ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_959,'#skF_7'))
      | r1_lattice3('#skF_5',B_959,'#skF_2'('#skF_5',B_959,'#skF_7'))
      | r2_yellow_0('#skF_5',B_959)
      | ~ r1_lattice3('#skF_5',B_959,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6030,c_26])).

tff(c_6055,plain,(
    ! [B_961] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_961,'#skF_7'))
      | r1_lattice3('#skF_5',B_961,'#skF_2'('#skF_5',B_961,'#skF_7'))
      | r2_yellow_0('#skF_5',B_961)
      | ~ r1_lattice3('#skF_5',B_961,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_40,c_6033])).

tff(c_6060,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_6055])).

tff(c_6067,plain,
    ( r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5784,c_5782,c_6060])).

tff(c_6068,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_6067])).

tff(c_5905,plain,(
    ! [A_930,B_931,C_932] :
      ( r1_lattice3(A_930,B_931,'#skF_1'(A_930,B_931,C_932))
      | m1_subset_1('#skF_2'(A_930,B_931,C_932),u1_struct_0(A_930))
      | r2_yellow_0(A_930,B_931)
      | ~ r1_lattice3(A_930,B_931,C_932)
      | ~ m1_subset_1(C_932,u1_struct_0(A_930))
      | ~ l1_orders_2(A_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5909,plain,(
    ! [B_931,C_932] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_931,C_932),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_931,C_932))
      | r1_lattice3('#skF_5',B_931,'#skF_1'('#skF_5',B_931,C_932))
      | r2_yellow_0('#skF_5',B_931)
      | ~ r1_lattice3('#skF_5',B_931,C_932)
      | ~ m1_subset_1(C_932,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5905,c_5787])).

tff(c_5994,plain,(
    ! [B_953,C_954] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_953,C_954),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_953,C_954))
      | r1_lattice3('#skF_5',B_953,'#skF_1'('#skF_5',B_953,C_954))
      | r2_yellow_0('#skF_5',B_953)
      | ~ r1_lattice3('#skF_5',B_953,C_954)
      | ~ m1_subset_1(C_954,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5909])).

tff(c_5996,plain,(
    ! [B_953,C_954] :
      ( '#skF_2'('#skF_5',B_953,C_954) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_953,C_954))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_953,C_954),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_953,C_954))
      | r1_lattice3('#skF_5',B_953,'#skF_1'('#skF_5',B_953,C_954))
      | r2_yellow_0('#skF_5',B_953)
      | ~ r1_lattice3('#skF_5',B_953,C_954)
      | ~ m1_subset_1(C_954,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5994,c_38])).

tff(c_6471,plain,(
    ! [B_1001,C_1002] :
      ( '#skF_2'('#skF_5',B_1001,C_1002) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_1001,C_1002))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1001,C_1002),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_1001,C_1002))
      | r1_lattice3('#skF_5',B_1001,'#skF_1'('#skF_5',B_1001,C_1002))
      | r2_yellow_0('#skF_5',B_1001)
      | ~ r1_lattice3('#skF_5',B_1001,C_1002)
      | ~ m1_subset_1(C_1002,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5784,c_5996])).

tff(c_6478,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_6471])).

tff(c_6486,plain,(
    ! [B_1003,C_1004] :
      ( '#skF_2'('#skF_5',B_1003,C_1004) = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_1003,C_1004))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_1003,C_1004))
      | r1_lattice3('#skF_5',B_1003,'#skF_1'('#skF_5',B_1003,C_1004))
      | r2_yellow_0('#skF_5',B_1003)
      | ~ r1_lattice3('#skF_5',B_1003,C_1004)
      | ~ m1_subset_1(C_1004,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6478])).

tff(c_6492,plain,(
    ! [B_39,C_58] :
      ( '#skF_2'('#skF_5',B_39,C_58) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_39,C_58))
      | r1_lattice3('#skF_5',B_39,'#skF_1'('#skF_5',B_39,C_58))
      | ~ r1_lattice3('#skF_5',B_39,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_39)
      | ~ r1_lattice3('#skF_5',B_39,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_6486])).

tff(c_6519,plain,(
    ! [B_1008,C_1009] :
      ( '#skF_2'('#skF_5',B_1008,C_1009) = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_1008,C_1009))
      | r1_lattice3('#skF_5',B_1008,'#skF_1'('#skF_5',B_1008,C_1009))
      | ~ r1_lattice3('#skF_5',B_1008,'#skF_7')
      | r2_yellow_0('#skF_5',B_1008)
      | ~ r1_lattice3('#skF_5',B_1008,C_1009)
      | ~ m1_subset_1(C_1009,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5784,c_6492])).

tff(c_6521,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6068,c_6519])).

tff(c_6526,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_5782,c_6521])).

tff(c_6527,plain,(
    r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5978,c_6526])).

tff(c_6125,plain,(
    ! [A_968,B_969,C_970,E_971] :
      ( m1_subset_1('#skF_1'(A_968,B_969,C_970),u1_struct_0(A_968))
      | r1_orders_2(A_968,E_971,'#skF_2'(A_968,B_969,C_970))
      | ~ r1_lattice3(A_968,B_969,E_971)
      | ~ m1_subset_1(E_971,u1_struct_0(A_968))
      | r2_yellow_0(A_968,B_969)
      | ~ r1_lattice3(A_968,B_969,C_970)
      | ~ m1_subset_1(C_970,u1_struct_0(A_968))
      | ~ l1_orders_2(A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6129,plain,(
    ! [B_969,C_970,E_971] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_969,C_970),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_969,C_970))
      | r1_orders_2('#skF_5',E_971,'#skF_2'('#skF_5',B_969,C_970))
      | ~ r1_lattice3('#skF_5',B_969,E_971)
      | ~ m1_subset_1(E_971,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_969)
      | ~ r1_lattice3('#skF_5',B_969,C_970)
      | ~ m1_subset_1(C_970,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6125,c_5787])).

tff(c_6173,plain,(
    ! [B_974,C_975,E_976] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_974,C_975),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_974,C_975))
      | r1_orders_2('#skF_5',E_976,'#skF_2'('#skF_5',B_974,C_975))
      | ~ r1_lattice3('#skF_5',B_974,E_976)
      | ~ m1_subset_1(E_976,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_974)
      | ~ r1_lattice3('#skF_5',B_974,C_975)
      | ~ m1_subset_1(C_975,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6129])).

tff(c_6176,plain,(
    ! [E_64,B_974,E_976] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_974,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_974,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_974,'#skF_7'))
      | r1_orders_2('#skF_5',E_976,'#skF_2'('#skF_5',B_974,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_974,E_976)
      | ~ m1_subset_1(E_976,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_974)
      | ~ r1_lattice3('#skF_5',B_974,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6173,c_20])).

tff(c_6213,plain,(
    ! [E_64,B_974,E_976] :
      ( r1_orders_2('#skF_5',E_64,'#skF_2'('#skF_5',B_974,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_974,E_64)
      | ~ m1_subset_1(E_64,u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_974,'#skF_7'))
      | r1_orders_2('#skF_5',E_976,'#skF_2'('#skF_5',B_974,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_974,E_976)
      | ~ m1_subset_1(E_976,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_974)
      | ~ r1_lattice3('#skF_5',B_974,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_40,c_6176])).

tff(c_6700,plain,(
    ! [B_1017,E_1018] :
      ( ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_1017,'#skF_7'))
      | ~ r1_lattice3('#skF_5',B_1017,E_1018)
      | ~ m1_subset_1(E_1018,u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_1017)
      | ~ r1_lattice3('#skF_5',B_1017,'#skF_7')
      | r1_orders_2('#skF_5',E_1018,'#skF_2'('#skF_5',B_1017,'#skF_7')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6213])).

tff(c_5926,plain,(
    ! [A_939,B_940,C_941] :
      ( m1_subset_1('#skF_1'(A_939,B_940,C_941),u1_struct_0(A_939))
      | m1_subset_1('#skF_2'(A_939,B_940,C_941),u1_struct_0(A_939))
      | r2_yellow_0(A_939,B_940)
      | ~ r1_lattice3(A_939,B_940,C_941)
      | ~ m1_subset_1(C_941,u1_struct_0(A_939))
      | ~ l1_orders_2(A_939) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5930,plain,(
    ! [B_940,C_941] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_940,C_941),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_940,C_941))
      | m1_subset_1('#skF_2'('#skF_5',B_940,C_941),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_940)
      | ~ r1_lattice3('#skF_5',B_940,C_941)
      | ~ m1_subset_1(C_941,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5926,c_5787])).

tff(c_5933,plain,(
    ! [B_940,C_941] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_940,C_941),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_940,C_941))
      | m1_subset_1('#skF_2'('#skF_5',B_940,C_941),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_940)
      | ~ r1_lattice3('#skF_5',B_940,C_941)
      | ~ m1_subset_1(C_941,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5930])).

tff(c_5989,plain,(
    ! [B_951,C_952] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5',B_951,C_952),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_951,C_952))
      | m1_subset_1('#skF_2'('#skF_5',B_951,C_952),u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_951)
      | ~ r1_lattice3('#skF_5',B_951,C_952)
      | ~ m1_subset_1(C_952,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5930])).

tff(c_6073,plain,(
    ! [B_962,C_963] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_962,C_963),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_962,C_963))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_962,C_963),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_962,C_963))
      | r2_yellow_0('#skF_5',B_962)
      | ~ r1_lattice3('#skF_5',B_962,C_963)
      | ~ m1_subset_1(C_963,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5989,c_5787])).

tff(c_6079,plain,(
    ! [B_962] :
      ( m1_subset_1('#skF_2'('#skF_5',B_962,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_962,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_962,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_962,'#skF_7'))
      | r2_yellow_0('#skF_5',B_962)
      | ~ r1_lattice3('#skF_5',B_962,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6073,c_32])).

tff(c_6162,plain,(
    ! [B_972] :
      ( m1_subset_1('#skF_2'('#skF_5',B_972,'#skF_7'),u1_struct_0('#skF_5'))
      | r1_orders_2('#skF_5','#skF_2'('#skF_5',B_972,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_972,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_972,'#skF_7'))
      | r2_yellow_0('#skF_5',B_972)
      | ~ r1_lattice3('#skF_5',B_972,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_40,c_6079])).

tff(c_6167,plain,(
    ! [B_973] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_973,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_973,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_973,'#skF_7'))
      | r2_yellow_0('#skF_5',B_973)
      | ~ r1_lattice3('#skF_5',B_973,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6162,c_5787])).

tff(c_6169,plain,(
    ! [B_973] :
      ( '#skF_2'('#skF_5',B_973,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_973,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_973,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_973,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_973,'#skF_7'))
      | r2_yellow_0('#skF_5',B_973)
      | ~ r1_lattice3('#skF_5',B_973,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6167,c_38])).

tff(c_6300,plain,(
    ! [B_982] :
      ( '#skF_2'('#skF_5',B_982,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_982,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_982,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_982,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_982,'#skF_7'))
      | r2_yellow_0('#skF_5',B_982)
      | ~ r1_lattice3('#skF_5',B_982,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5784,c_6169])).

tff(c_6307,plain,(
    ! [B_940] :
      ( '#skF_2'('#skF_5',B_940,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_940,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_940,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_940,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_940,'#skF_7'))
      | r2_yellow_0('#skF_5',B_940)
      | ~ r1_lattice3('#skF_5',B_940,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5933,c_6300])).

tff(c_6319,plain,(
    ! [B_983] :
      ( '#skF_2'('#skF_5',B_983,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_983,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_983,'#skF_7'))
      | r1_orders_2('#skF_5','#skF_1'('#skF_5',B_983,'#skF_7'),'#skF_7')
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_983,'#skF_7'))
      | r2_yellow_0('#skF_5',B_983)
      | ~ r1_lattice3('#skF_5',B_983,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_6307])).

tff(c_6325,plain,(
    ! [B_983] :
      ( m1_subset_1('#skF_2'('#skF_5',B_983,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | '#skF_2'('#skF_5',B_983,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_983,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_983,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_983,'#skF_7'))
      | r2_yellow_0('#skF_5',B_983)
      | ~ r1_lattice3('#skF_5',B_983,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6319,c_32])).

tff(c_6374,plain,(
    ! [B_986] :
      ( m1_subset_1('#skF_2'('#skF_5',B_986,'#skF_7'),u1_struct_0('#skF_5'))
      | '#skF_2'('#skF_5',B_986,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_986,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_986,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_986,'#skF_7'))
      | r2_yellow_0('#skF_5',B_986)
      | ~ r1_lattice3('#skF_5',B_986,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5784,c_6325])).

tff(c_6172,plain,(
    ! [B_973] :
      ( '#skF_2'('#skF_5',B_973,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_973,'#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_973,'#skF_7'),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_973,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_973,'#skF_7'))
      | r2_yellow_0('#skF_5',B_973)
      | ~ r1_lattice3('#skF_5',B_973,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5784,c_6169])).

tff(c_6381,plain,(
    ! [B_986] :
      ( '#skF_2'('#skF_5',B_986,'#skF_7') = '#skF_7'
      | ~ r1_orders_2('#skF_5','#skF_7','#skF_2'('#skF_5',B_986,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_986,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_986,'#skF_7'))
      | r2_yellow_0('#skF_5',B_986)
      | ~ r1_lattice3('#skF_5',B_986,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6374,c_6172])).

tff(c_6707,plain,(
    ! [B_1017] :
      ( '#skF_2'('#skF_5',B_1017,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_1017,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_1017,'#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | r2_yellow_0('#skF_5',B_1017)
      | ~ r1_lattice3('#skF_5',B_1017,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6700,c_6381])).

tff(c_6757,plain,(
    ! [B_1019] :
      ( '#skF_2'('#skF_5',B_1019,'#skF_7') = '#skF_7'
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5',B_1019,'#skF_7'))
      | ~ r1_lattice3('#skF_5','#skF_6','#skF_1'('#skF_5',B_1019,'#skF_7'))
      | r2_yellow_0('#skF_5',B_1019)
      | ~ r1_lattice3('#skF_5',B_1019,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5784,c_6707])).

tff(c_6760,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_6','#skF_7'))
    | r2_yellow_0('#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6527,c_6757])).

tff(c_6777,plain,
    ( '#skF_2'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | r2_yellow_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_6068,c_6760])).

tff(c_6779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5978,c_6777])).

tff(c_6780,plain,(
    r2_yellow_0('#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6781,plain,(
    r2_yellow_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_52,plain,(
    ! [C_100] :
      ( ~ r2_yellow_0('#skF_5','#skF_6')
      | r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6791,plain,(
    ! [C_100] :
      ( r1_lattice3('#skF_5','#skF_8','#skF_9'(C_100))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6781,c_52])).

tff(c_6796,plain,(
    ! [A_1027,D_1028,B_1029] :
      ( r1_orders_2(A_1027,D_1028,'#skF_3'(A_1027,B_1029))
      | ~ r1_lattice3(A_1027,B_1029,D_1028)
      | ~ m1_subset_1(D_1028,u1_struct_0(A_1027))
      | ~ r2_yellow_0(A_1027,B_1029)
      | ~ l1_orders_2(A_1027) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [C_100] :
      ( ~ r2_yellow_0('#skF_5','#skF_6')
      | ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6788,plain,(
    ! [C_100] :
      ( ~ r1_orders_2('#skF_5','#skF_9'(C_100),C_100)
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6781,c_44])).

tff(c_6800,plain,(
    ! [B_1029] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_1029))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_1029),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_1029,'#skF_9'('#skF_3'('#skF_5',B_1029)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_1029)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_1029)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6796,c_6788])).

tff(c_6822,plain,(
    ! [B_1045] :
      ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5',B_1045))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_1045),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5',B_1045,'#skF_9'('#skF_3'('#skF_5',B_1045)))
      | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5',B_1045)),u1_struct_0('#skF_5'))
      | ~ r2_yellow_0('#skF_5',B_1045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6800])).

tff(c_6825,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6791,c_6822])).

tff(c_6828,plain,
    ( ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5'))
    | ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6780,c_6825])).

tff(c_6829,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6828])).

tff(c_6832,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_6829])).

tff(c_6836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6780,c_6832])).

tff(c_6838,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6828])).

tff(c_60,plain,(
    ! [C_100] :
      ( ~ r2_yellow_0('#skF_5','#skF_6')
      | m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6794,plain,(
    ! [C_100] :
      ( m1_subset_1('#skF_9'(C_100),u1_struct_0('#skF_5'))
      | ~ r1_lattice3('#skF_5','#skF_8',C_100)
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6781,c_60])).

tff(c_6837,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6828])).

tff(c_6839,plain,(
    ~ m1_subset_1('#skF_9'('#skF_3'('#skF_5','#skF_8')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6837])).

tff(c_6842,plain,
    ( ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6794,c_6839])).

tff(c_6845,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6838,c_6842])).

tff(c_6849,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6845])).

tff(c_6853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6780,c_6849])).

tff(c_6854,plain,(
    ~ r1_lattice3('#skF_5','#skF_8','#skF_3'('#skF_5','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6837])).

tff(c_6858,plain,
    ( ~ r2_yellow_0('#skF_5','#skF_8')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6854])).

tff(c_6862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6780,c_6858])).

%------------------------------------------------------------------------------
