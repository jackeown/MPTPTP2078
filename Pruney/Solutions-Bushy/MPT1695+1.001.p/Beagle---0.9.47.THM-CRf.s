%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1695+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:15 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  162 (4748 expanded)
%              Number of leaves         :   31 (1623 expanded)
%              Depth                    :   30
%              Number of atoms          :  632 (23551 expanded)
%              Number of equality atoms :   25 ( 167 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > v1_waybel_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v24_waybel_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v24_waybel_0,type,(
    v24_waybel_0: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ( v24_waybel_0(A)
        <=> ! [B] :
              ( ( ~ v1_xboole_0(B)
                & v1_waybel_0(B,A)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
             => r1_yellow_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_waybel_0)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ( v24_waybel_0(A)
      <=> ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r3_orders_2(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d39_waybel_0)).

tff(f_84,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_115,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_76,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v24_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_89,plain,(
    ~ v24_waybel_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_66,plain,(
    v3_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_62,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_waybel_0('#skF_2'(A_1),A_1)
      | v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [A_118] :
      ( m1_subset_1('#skF_2'(A_118),k1_zfmisc_1(u1_struct_0(A_118)))
      | v24_waybel_0(A_118)
      | ~ l1_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [B_110] :
      ( v24_waybel_0('#skF_8')
      | r1_yellow_0('#skF_8',B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ v1_waybel_0(B_110,'#skF_8')
      | v1_xboole_0(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_90,plain,(
    ! [B_110] :
      ( r1_yellow_0('#skF_8',B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ v1_waybel_0(B_110,'#skF_8')
      | v1_xboole_0(B_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_88])).

tff(c_100,plain,
    ( r1_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | ~ v1_waybel_0('#skF_2'('#skF_8'),'#skF_8')
    | v1_xboole_0('#skF_2'('#skF_8'))
    | v24_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_90])).

tff(c_103,plain,
    ( r1_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | ~ v1_waybel_0('#skF_2'('#skF_8'),'#skF_8')
    | v1_xboole_0('#skF_2'('#skF_8'))
    | v24_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_100])).

tff(c_104,plain,
    ( r1_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | ~ v1_waybel_0('#skF_2'('#skF_8'),'#skF_8')
    | v1_xboole_0('#skF_2'('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_89,c_103])).

tff(c_105,plain,(
    ~ v1_waybel_0('#skF_2'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_108,plain,
    ( v24_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_111,plain,
    ( v24_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_108])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_89,c_111])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_2'('#skF_8'))
    | r1_yellow_0('#skF_8','#skF_2'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_116,plain,(
    r1_yellow_0('#skF_8','#skF_2'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_24,plain,(
    ! [A_27,B_65] :
      ( m1_subset_1('#skF_6'(A_27,B_65),u1_struct_0(A_27))
      | ~ r1_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_27,B_65] :
      ( r2_lattice3(A_27,B_65,'#skF_6'(A_27,B_65))
      | ~ r1_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_1,C_25] :
      ( m1_subset_1('#skF_3'(A_1,C_25),u1_struct_0(A_1))
      | ~ r2_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_1,C_25] :
      ( r2_lattice3(A_1,'#skF_2'(A_1),'#skF_3'(A_1,C_25))
      | ~ r2_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_27,B_65,D_95] :
      ( r1_orders_2(A_27,'#skF_6'(A_27,B_65),D_95)
      | ~ r2_lattice3(A_27,B_65,D_95)
      | ~ m1_subset_1(D_95,u1_struct_0(A_27))
      | ~ r1_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_128,plain,(
    ! [A_133,C_134] :
      ( m1_subset_1('#skF_3'(A_133,C_134),u1_struct_0(A_133))
      | ~ r2_lattice3(A_133,'#skF_2'(A_133),C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | v24_waybel_0(A_133)
      | ~ l1_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [A_98,B_99,C_100] :
      ( r3_orders_2(A_98,B_99,C_100)
      | ~ r1_orders_2(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_199,plain,(
    ! [A_186,B_187,C_188] :
      ( r3_orders_2(A_186,B_187,'#skF_3'(A_186,C_188))
      | ~ r1_orders_2(A_186,B_187,'#skF_3'(A_186,C_188))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ r2_lattice3(A_186,'#skF_2'(A_186),C_188)
      | ~ m1_subset_1(C_188,u1_struct_0(A_186))
      | v24_waybel_0(A_186)
      | ~ l1_orders_2(A_186)
      | ~ v3_orders_2(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_128,c_56])).

tff(c_8,plain,(
    ! [A_1,C_25] :
      ( ~ r3_orders_2(A_1,C_25,'#skF_3'(A_1,C_25))
      | ~ r2_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_213,plain,(
    ! [A_193,C_194] :
      ( ~ r1_orders_2(A_193,C_194,'#skF_3'(A_193,C_194))
      | ~ r2_lattice3(A_193,'#skF_2'(A_193),C_194)
      | ~ m1_subset_1(C_194,u1_struct_0(A_193))
      | v24_waybel_0(A_193)
      | ~ l1_orders_2(A_193)
      | ~ v3_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_199,c_8])).

tff(c_306,plain,(
    ! [A_217,B_218] :
      ( ~ r2_lattice3(A_217,'#skF_2'(A_217),'#skF_6'(A_217,B_218))
      | ~ m1_subset_1('#skF_6'(A_217,B_218),u1_struct_0(A_217))
      | v24_waybel_0(A_217)
      | ~ v3_orders_2(A_217)
      | v2_struct_0(A_217)
      | ~ r2_lattice3(A_217,B_218,'#skF_3'(A_217,'#skF_6'(A_217,B_218)))
      | ~ m1_subset_1('#skF_3'(A_217,'#skF_6'(A_217,B_218)),u1_struct_0(A_217))
      | ~ r1_yellow_0(A_217,B_218)
      | ~ l1_orders_2(A_217) ) ),
    inference(resolution,[status(thm)],[c_20,c_213])).

tff(c_311,plain,(
    ! [A_219] :
      ( ~ m1_subset_1('#skF_3'(A_219,'#skF_6'(A_219,'#skF_2'(A_219))),u1_struct_0(A_219))
      | ~ r1_yellow_0(A_219,'#skF_2'(A_219))
      | ~ r2_lattice3(A_219,'#skF_2'(A_219),'#skF_6'(A_219,'#skF_2'(A_219)))
      | ~ m1_subset_1('#skF_6'(A_219,'#skF_2'(A_219)),u1_struct_0(A_219))
      | v24_waybel_0(A_219)
      | ~ l1_orders_2(A_219)
      | ~ v3_orders_2(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_10,c_306])).

tff(c_317,plain,(
    ! [A_220] :
      ( ~ r1_yellow_0(A_220,'#skF_2'(A_220))
      | ~ r2_lattice3(A_220,'#skF_2'(A_220),'#skF_6'(A_220,'#skF_2'(A_220)))
      | ~ m1_subset_1('#skF_6'(A_220,'#skF_2'(A_220)),u1_struct_0(A_220))
      | v24_waybel_0(A_220)
      | ~ l1_orders_2(A_220)
      | ~ v3_orders_2(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_12,c_311])).

tff(c_323,plain,(
    ! [A_221] :
      ( ~ m1_subset_1('#skF_6'(A_221,'#skF_2'(A_221)),u1_struct_0(A_221))
      | v24_waybel_0(A_221)
      | ~ v3_orders_2(A_221)
      | v2_struct_0(A_221)
      | ~ r1_yellow_0(A_221,'#skF_2'(A_221))
      | ~ l1_orders_2(A_221) ) ),
    inference(resolution,[status(thm)],[c_22,c_317])).

tff(c_329,plain,(
    ! [A_222] :
      ( v24_waybel_0(A_222)
      | ~ v3_orders_2(A_222)
      | v2_struct_0(A_222)
      | ~ r1_yellow_0(A_222,'#skF_2'(A_222))
      | ~ l1_orders_2(A_222) ) ),
    inference(resolution,[status(thm)],[c_24,c_323])).

tff(c_332,plain,
    ( v24_waybel_0('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_116,c_329])).

tff(c_335,plain,
    ( v24_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_66,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_89,c_335])).

tff(c_338,plain,(
    v1_xboole_0('#skF_2'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_6,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_2'(A_1))
      | v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_342,plain,
    ( v24_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_338,c_6])).

tff(c_345,plain,
    ( v24_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_342])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_89,c_345])).

tff(c_349,plain,(
    v24_waybel_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_70,plain,
    ( ~ r1_yellow_0('#skF_8','#skF_9')
    | ~ v24_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_351,plain,(
    ~ r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_70])).

tff(c_348,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,
    ( v1_waybel_0('#skF_9','#skF_8')
    | ~ v24_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_353,plain,(
    v1_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_74])).

tff(c_72,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ v24_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_355,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_72])).

tff(c_383,plain,(
    ! [A_248,B_249] :
      ( r2_lattice3(A_248,B_249,'#skF_1'(A_248,B_249))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ v1_waybel_0(B_249,A_248)
      | v1_xboole_0(B_249)
      | ~ v24_waybel_0(A_248)
      | ~ l1_orders_2(A_248)
      | ~ v3_orders_2(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_387,plain,
    ( r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ v1_waybel_0('#skF_9','#skF_8')
    | v1_xboole_0('#skF_9')
    | ~ v24_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_355,c_383])).

tff(c_391,plain,
    ( r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | v1_xboole_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_349,c_353,c_387])).

tff(c_392,plain,(
    r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_348,c_391])).

tff(c_18,plain,(
    ! [A_1,B_16] :
      ( m1_subset_1('#skF_1'(A_1,B_16),u1_struct_0(A_1))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v1_waybel_0(B_16,A_1)
      | v1_xboole_0(B_16)
      | ~ v24_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_448,plain,(
    ! [A_294,B_295,D_296] :
      ( r3_orders_2(A_294,'#skF_1'(A_294,B_295),D_296)
      | ~ r2_lattice3(A_294,B_295,D_296)
      | ~ m1_subset_1(D_296,u1_struct_0(A_294))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ v1_waybel_0(B_295,A_294)
      | v1_xboole_0(B_295)
      | ~ v24_waybel_0(A_294)
      | ~ l1_orders_2(A_294)
      | ~ v3_orders_2(A_294)
      | v2_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_452,plain,(
    ! [D_296] :
      ( r3_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_296)
      | ~ r2_lattice3('#skF_8','#skF_9',D_296)
      | ~ m1_subset_1(D_296,u1_struct_0('#skF_8'))
      | ~ v1_waybel_0('#skF_9','#skF_8')
      | v1_xboole_0('#skF_9')
      | ~ v24_waybel_0('#skF_8')
      | ~ l1_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_355,c_448])).

tff(c_456,plain,(
    ! [D_296] :
      ( r3_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_296)
      | ~ r2_lattice3('#skF_8','#skF_9',D_296)
      | ~ m1_subset_1(D_296,u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_349,c_353,c_452])).

tff(c_458,plain,(
    ! [D_297] :
      ( r3_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_297)
      | ~ r2_lattice3('#skF_8','#skF_9',D_297)
      | ~ m1_subset_1(D_297,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_348,c_456])).

tff(c_58,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_orders_2(A_98,B_99,C_100)
      | ~ r3_orders_2(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_464,plain,(
    ! [D_297] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_297)
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9',D_297)
      | ~ m1_subset_1(D_297,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_458,c_58])).

tff(c_471,plain,(
    ! [D_297] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_297)
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9',D_297)
      | ~ m1_subset_1(D_297,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_464])).

tff(c_472,plain,(
    ! [D_297] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_297)
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_lattice3('#skF_8','#skF_9',D_297)
      | ~ m1_subset_1(D_297,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_471])).

tff(c_473,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_502,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ v1_waybel_0('#skF_9','#skF_8')
    | v1_xboole_0('#skF_9')
    | ~ v24_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_18,c_473])).

tff(c_505,plain,
    ( v1_xboole_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_349,c_353,c_355,c_502])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_348,c_505])).

tff(c_509,plain,(
    m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_34,plain,(
    ! [A_27,B_65,C_84] :
      ( r2_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_516,plain,(
    ! [D_302] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_302)
      | ~ r2_lattice3('#skF_8','#skF_9',D_302)
      | ~ m1_subset_1(D_302,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_32,plain,(
    ! [A_27,C_84,B_65] :
      ( ~ r1_orders_2(A_27,C_84,'#skF_4'(A_27,B_65,C_84))
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_529,plain,(
    ! [B_65] :
      ( '#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_516,c_32])).

tff(c_637,plain,(
    ! [B_318] :
      ( '#skF_5'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r1_yellow_0('#skF_8',B_318)
      | ~ r2_lattice3('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_529])).

tff(c_649,plain,(
    ! [B_65] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | '#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_637])).

tff(c_659,plain,(
    ! [B_319] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_319,'#skF_1'('#skF_8','#skF_9')))
      | '#skF_5'('#skF_8',B_319,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r1_yellow_0('#skF_8',B_319)
      | ~ r2_lattice3('#skF_8',B_319,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_649])).

tff(c_669,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
    | r1_yellow_0('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_659])).

tff(c_676,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
    | r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_392,c_669])).

tff(c_677,plain,(
    '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_676])).

tff(c_46,plain,(
    ! [A_27,B_65,C_84] :
      ( r2_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | r2_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r2_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_27,C_84,B_65] :
      ( ~ r1_orders_2(A_27,C_84,'#skF_4'(A_27,B_65,C_84))
      | r2_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_522,plain,(
    ! [B_65] :
      ( r2_lattice3('#skF_8',B_65,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_516,c_44])).

tff(c_781,plain,(
    ! [B_331] :
      ( r2_lattice3('#skF_8',B_331,'#skF_5'('#skF_8',B_331,'#skF_1'('#skF_8','#skF_9')))
      | r1_yellow_0('#skF_8',B_331)
      | ~ r2_lattice3('#skF_8',B_331,'#skF_1'('#skF_8','#skF_9'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_331,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_331,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_522])).

tff(c_790,plain,(
    ! [B_65] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r2_lattice3('#skF_8',B_65,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_781])).

tff(c_806,plain,(
    ! [B_332] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_332,'#skF_1'('#skF_8','#skF_9')))
      | r2_lattice3('#skF_8',B_332,'#skF_5'('#skF_8',B_332,'#skF_1'('#skF_8','#skF_9')))
      | r1_yellow_0('#skF_8',B_332)
      | ~ r2_lattice3('#skF_8',B_332,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_790])).

tff(c_813,plain,
    ( r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_806])).

tff(c_823,plain,
    ( r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_392,c_813])).

tff(c_824,plain,(
    r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_823])).

tff(c_52,plain,(
    ! [A_27,B_65,C_84] :
      ( r2_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_732,plain,(
    ! [A_327,B_328,C_329,E_330] :
      ( r2_lattice3(A_327,B_328,'#skF_4'(A_327,B_328,C_329))
      | r1_orders_2(A_327,'#skF_5'(A_327,B_328,C_329),E_330)
      | ~ r2_lattice3(A_327,B_328,E_330)
      | ~ m1_subset_1(E_330,u1_struct_0(A_327))
      | r1_yellow_0(A_327,B_328)
      | ~ r2_lattice3(A_327,B_328,C_329)
      | ~ m1_subset_1(C_329,u1_struct_0(A_327))
      | ~ l1_orders_2(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_60,plain,(
    ! [C_107,B_105,A_101] :
      ( C_107 = B_105
      | ~ r1_orders_2(A_101,C_107,B_105)
      | ~ r1_orders_2(A_101,B_105,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_101))
      | ~ m1_subset_1(B_105,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_535,plain,(
    ! [D_302] :
      ( D_302 = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_8',D_302,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9',D_302)
      | ~ m1_subset_1(D_302,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_516,c_60])).

tff(c_553,plain,(
    ! [D_302] :
      ( D_302 = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_8',D_302,'#skF_1'('#skF_8','#skF_9'))
      | ~ r2_lattice3('#skF_8','#skF_9',D_302)
      | ~ m1_subset_1(D_302,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_509,c_535])).

tff(c_746,plain,(
    ! [B_328,C_329] :
      ( '#skF_5'('#skF_8',B_328,C_329) = '#skF_1'('#skF_8','#skF_9')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_328,C_329))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_328,C_329),u1_struct_0('#skF_8'))
      | r2_lattice3('#skF_8',B_328,'#skF_4'('#skF_8',B_328,C_329))
      | ~ r2_lattice3('#skF_8',B_328,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_328)
      | ~ r2_lattice3('#skF_8',B_328,C_329)
      | ~ m1_subset_1(C_329,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_732,c_553])).

tff(c_959,plain,(
    ! [B_371,C_372] :
      ( '#skF_5'('#skF_8',B_371,C_372) = '#skF_1'('#skF_8','#skF_9')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_371,C_372))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_371,C_372),u1_struct_0('#skF_8'))
      | r2_lattice3('#skF_8',B_371,'#skF_4'('#skF_8',B_371,C_372))
      | ~ r2_lattice3('#skF_8',B_371,'#skF_1'('#skF_8','#skF_9'))
      | r1_yellow_0('#skF_8',B_371)
      | ~ r2_lattice3('#skF_8',B_371,C_372)
      | ~ m1_subset_1(C_372,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_746])).

tff(c_967,plain,(
    ! [B_65,C_84] :
      ( '#skF_5'('#skF_8',B_65,C_84) = '#skF_1'('#skF_8','#skF_9')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_65,C_84))
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | r2_lattice3('#skF_8',B_65,'#skF_4'('#skF_8',B_65,C_84))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_959])).

tff(c_978,plain,(
    ! [B_373,C_374] :
      ( '#skF_5'('#skF_8',B_373,C_374) = '#skF_1'('#skF_8','#skF_9')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_373,C_374))
      | ~ r2_lattice3('#skF_8',B_373,'#skF_1'('#skF_8','#skF_9'))
      | r2_lattice3('#skF_8',B_373,'#skF_4'('#skF_8',B_373,C_374))
      | r1_yellow_0('#skF_8',B_373)
      | ~ r2_lattice3('#skF_8',B_373,C_374)
      | ~ m1_subset_1(C_374,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_967])).

tff(c_981,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_824,c_978])).

tff(c_985,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_392,c_981])).

tff(c_986,plain,(
    r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_677,c_985])).

tff(c_54,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_27,C_84,B_65] :
      ( ~ r1_orders_2(A_27,C_84,'#skF_4'(A_27,B_65,C_84))
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_525,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_516,c_50])).

tff(c_830,plain,(
    ! [B_333] :
      ( m1_subset_1('#skF_5'('#skF_8',B_333,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_333)
      | ~ r2_lattice3('#skF_8',B_333,'#skF_1'('#skF_8','#skF_9'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_333,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_333,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_525])).

tff(c_838,plain,(
    ! [B_65] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_830])).

tff(c_852,plain,(
    ! [B_65] :
      ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_838])).

tff(c_42,plain,(
    ! [A_27,B_65,C_84,E_90] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_orders_2(A_27,'#skF_5'(A_27,B_65,C_84),E_90)
      | ~ r2_lattice3(A_27,B_65,E_90)
      | ~ m1_subset_1(E_90,u1_struct_0(A_27))
      | r1_yellow_0(A_27,B_65)
      | ~ r2_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_508,plain,(
    ! [D_297] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_297)
      | ~ r2_lattice3('#skF_8','#skF_9',D_297)
      | ~ m1_subset_1(D_297,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_598,plain,(
    ! [A_310,C_311,B_312,E_313] :
      ( ~ r1_orders_2(A_310,C_311,'#skF_4'(A_310,B_312,C_311))
      | r1_orders_2(A_310,'#skF_5'(A_310,B_312,C_311),E_313)
      | ~ r2_lattice3(A_310,B_312,E_313)
      | ~ m1_subset_1(E_313,u1_struct_0(A_310))
      | r1_yellow_0(A_310,B_312)
      | ~ r2_lattice3(A_310,B_312,C_311)
      | ~ m1_subset_1(C_311,u1_struct_0(A_310))
      | ~ l1_orders_2(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_601,plain,(
    ! [B_312,E_313] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8',B_312,'#skF_1'('#skF_8','#skF_9')),E_313)
      | ~ r2_lattice3('#skF_8',B_312,E_313)
      | ~ m1_subset_1(E_313,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_312)
      | ~ r2_lattice3('#skF_8',B_312,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_312,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_312,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_508,c_598])).

tff(c_934,plain,(
    ! [B_369,E_370] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8',B_369,'#skF_1'('#skF_8','#skF_9')),E_370)
      | ~ r2_lattice3('#skF_8',B_369,E_370)
      | ~ m1_subset_1(E_370,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_369)
      | ~ r2_lattice3('#skF_8',B_369,'#skF_1'('#skF_8','#skF_9'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_369,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_369,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_601])).

tff(c_937,plain,(
    ! [B_65,E_370,E_90] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),E_370)
      | ~ r2_lattice3('#skF_8',B_65,E_370)
      | ~ m1_subset_1(E_370,u1_struct_0('#skF_8'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_orders_2('#skF_8','#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),E_90)
      | ~ r2_lattice3('#skF_8',B_65,E_90)
      | ~ m1_subset_1(E_90,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_65)
      | ~ r2_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_934])).

tff(c_1216,plain,(
    ! [B_403,E_404,E_405] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8',B_403,'#skF_1'('#skF_8','#skF_9')),E_404)
      | ~ r2_lattice3('#skF_8',B_403,E_404)
      | ~ m1_subset_1(E_404,u1_struct_0('#skF_8'))
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_403,'#skF_1'('#skF_8','#skF_9')))
      | r1_orders_2('#skF_8','#skF_5'('#skF_8',B_403,'#skF_1'('#skF_8','#skF_9')),E_405)
      | ~ r2_lattice3('#skF_8',B_403,E_405)
      | ~ m1_subset_1(E_405,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',B_403)
      | ~ r2_lattice3('#skF_8',B_403,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_509,c_937])).

tff(c_1218,plain,(
    ! [E_404,E_405] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_404)
      | ~ r2_lattice3('#skF_8','#skF_9',E_404)
      | ~ m1_subset_1(E_404,u1_struct_0('#skF_8'))
      | r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_405)
      | ~ r2_lattice3('#skF_8','#skF_9',E_405)
      | ~ m1_subset_1(E_405,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8','#skF_9')
      | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_986,c_1216])).

tff(c_1232,plain,(
    ! [E_404,E_405] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_404)
      | ~ r2_lattice3('#skF_8','#skF_9',E_404)
      | ~ m1_subset_1(E_404,u1_struct_0('#skF_8'))
      | r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_405)
      | ~ r2_lattice3('#skF_8','#skF_9',E_405)
      | ~ m1_subset_1(E_405,u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_1218])).

tff(c_1233,plain,(
    ! [E_404,E_405] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_404)
      | ~ r2_lattice3('#skF_8','#skF_9',E_404)
      | ~ m1_subset_1(E_404,u1_struct_0('#skF_8'))
      | r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_405)
      | ~ r2_lattice3('#skF_8','#skF_9',E_405)
      | ~ m1_subset_1(E_405,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_1232])).

tff(c_1268,plain,(
    ! [E_410] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_410)
      | ~ r2_lattice3('#skF_8','#skF_9',E_410)
      | ~ m1_subset_1(E_410,u1_struct_0('#skF_8')) ) ),
    inference(splitLeft,[status(thm)],[c_1233])).

tff(c_1284,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1268,c_553])).

tff(c_1319,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_392,c_824,c_1284])).

tff(c_1320,plain,(
    ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_677,c_1319])).

tff(c_1344,plain,
    ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_852,c_1320])).

tff(c_1354,plain,(
    r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_986,c_1344])).

tff(c_1356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_1354])).

tff(c_1358,plain,(
    ! [E_411] :
      ( r1_orders_2('#skF_8','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),E_411)
      | ~ r2_lattice3('#skF_8','#skF_9',E_411)
      | ~ m1_subset_1(E_411,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_1233])).

tff(c_1374,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1358,c_553])).

tff(c_1409,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_392,c_824,c_1374])).

tff(c_1410,plain,(
    ~ m1_subset_1('#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_677,c_1409])).

tff(c_1434,plain,
    ( ~ r2_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r1_yellow_0('#skF_8','#skF_9')
    | ~ r2_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_852,c_1410])).

tff(c_1444,plain,(
    r1_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_986,c_1434])).

tff(c_1446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_1444])).

%------------------------------------------------------------------------------
