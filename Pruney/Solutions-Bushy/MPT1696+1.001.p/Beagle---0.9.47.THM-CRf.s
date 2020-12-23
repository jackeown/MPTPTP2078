%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:15 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  136 (1275 expanded)
%              Number of leaves         :   28 ( 447 expanded)
%              Depth                    :   21
%              Number of atoms          :  539 (6038 expanded)
%              Number of equality atoms :   28 ( 144 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v25_waybel_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v25_waybel_0,type,(
    v25_waybel_0: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ( v25_waybel_0(A)
        <=> ! [B] :
              ( ( ~ v1_xboole_0(B)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
             => r2_yellow_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_waybel_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ( v25_waybel_0(A)
      <=> ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d40_waybel_0)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

tff(f_98,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v25_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_79,plain,(
    ~ v25_waybel_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_56,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    v3_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_85,plain,(
    ! [A_114] :
      ( m1_subset_1('#skF_2'(A_114),k1_zfmisc_1(u1_struct_0(A_114)))
      | v25_waybel_0(A_114)
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [B_107] :
      ( v25_waybel_0('#skF_8')
      | r2_yellow_0('#skF_8',B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v1_xboole_0(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_81,plain,(
    ! [B_107] :
      ( r2_yellow_0('#skF_8',B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v1_xboole_0(B_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_78])).

tff(c_89,plain,
    ( r2_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | v1_xboole_0('#skF_2'('#skF_8'))
    | v25_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_81])).

tff(c_92,plain,
    ( r2_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | v1_xboole_0('#skF_2'('#skF_8'))
    | v25_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_89])).

tff(c_93,plain,
    ( r2_yellow_0('#skF_8','#skF_2'('#skF_8'))
    | v1_xboole_0('#skF_2'('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_79,c_92])).

tff(c_94,plain,(
    v1_xboole_0('#skF_2'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_4,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_2'(A_1))
      | v25_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( v25_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_100,plain,
    ( v25_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_97])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_79,c_100])).

tff(c_103,plain,(
    r2_yellow_0('#skF_8','#skF_2'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_22,plain,(
    ! [A_27,B_65] :
      ( m1_subset_1('#skF_6'(A_27,B_65),u1_struct_0(A_27))
      | ~ r2_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_27,B_65] :
      ( r1_lattice3(A_27,B_65,'#skF_6'(A_27,B_65))
      | ~ r2_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_1,C_25] :
      ( m1_subset_1('#skF_3'(A_1,C_25),u1_struct_0(A_1))
      | ~ r1_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | v25_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_1,C_25] :
      ( r1_lattice3(A_1,'#skF_2'(A_1),'#skF_3'(A_1,C_25))
      | ~ r1_lattice3(A_1,'#skF_2'(A_1),C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_1))
      | v25_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_27,D_95,B_65] :
      ( r1_orders_2(A_27,D_95,'#skF_6'(A_27,B_65))
      | ~ r1_lattice3(A_27,B_65,D_95)
      | ~ m1_subset_1(D_95,u1_struct_0(A_27))
      | ~ r2_yellow_0(A_27,B_65)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_116,plain,(
    ! [A_127,C_128] :
      ( ~ r1_orders_2(A_127,'#skF_3'(A_127,C_128),C_128)
      | ~ r1_lattice3(A_127,'#skF_2'(A_127),C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_127))
      | v25_waybel_0(A_127)
      | ~ l1_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_237,plain,(
    ! [A_185,B_186] :
      ( ~ r1_lattice3(A_185,'#skF_2'(A_185),'#skF_6'(A_185,B_186))
      | ~ m1_subset_1('#skF_6'(A_185,B_186),u1_struct_0(A_185))
      | v25_waybel_0(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185)
      | ~ r1_lattice3(A_185,B_186,'#skF_3'(A_185,'#skF_6'(A_185,B_186)))
      | ~ m1_subset_1('#skF_3'(A_185,'#skF_6'(A_185,B_186)),u1_struct_0(A_185))
      | ~ r2_yellow_0(A_185,B_186)
      | ~ l1_orders_2(A_185) ) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_248,plain,(
    ! [A_190] :
      ( ~ m1_subset_1('#skF_3'(A_190,'#skF_6'(A_190,'#skF_2'(A_190))),u1_struct_0(A_190))
      | ~ r2_yellow_0(A_190,'#skF_2'(A_190))
      | ~ r1_lattice3(A_190,'#skF_2'(A_190),'#skF_6'(A_190,'#skF_2'(A_190)))
      | ~ m1_subset_1('#skF_6'(A_190,'#skF_2'(A_190)),u1_struct_0(A_190))
      | v25_waybel_0(A_190)
      | ~ l1_orders_2(A_190)
      | ~ v3_orders_2(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_254,plain,(
    ! [A_191] :
      ( ~ r2_yellow_0(A_191,'#skF_2'(A_191))
      | ~ r1_lattice3(A_191,'#skF_2'(A_191),'#skF_6'(A_191,'#skF_2'(A_191)))
      | ~ m1_subset_1('#skF_6'(A_191,'#skF_2'(A_191)),u1_struct_0(A_191))
      | v25_waybel_0(A_191)
      | ~ l1_orders_2(A_191)
      | ~ v3_orders_2(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_10,c_248])).

tff(c_260,plain,(
    ! [A_192] :
      ( ~ m1_subset_1('#skF_6'(A_192,'#skF_2'(A_192)),u1_struct_0(A_192))
      | v25_waybel_0(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192)
      | ~ r2_yellow_0(A_192,'#skF_2'(A_192))
      | ~ l1_orders_2(A_192) ) ),
    inference(resolution,[status(thm)],[c_20,c_254])).

tff(c_266,plain,(
    ! [A_193] :
      ( v25_waybel_0(A_193)
      | ~ v3_orders_2(A_193)
      | v2_struct_0(A_193)
      | ~ r2_yellow_0(A_193,'#skF_2'(A_193))
      | ~ l1_orders_2(A_193) ) ),
    inference(resolution,[status(thm)],[c_22,c_260])).

tff(c_269,plain,
    ( v25_waybel_0('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_103,c_266])).

tff(c_272,plain,
    ( v25_waybel_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_269])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_79,c_272])).

tff(c_276,plain,(
    v25_waybel_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_64,plain,
    ( ~ r2_yellow_0('#skF_8','#skF_9')
    | ~ v25_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_278,plain,(
    ~ r2_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_64])).

tff(c_275,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ v25_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_280,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_66])).

tff(c_16,plain,(
    ! [A_1,B_16] :
      ( m1_subset_1('#skF_1'(A_1,B_16),u1_struct_0(A_1))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_xboole_0(B_16)
      | ~ v25_waybel_0(A_1)
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_341,plain,(
    ! [A_252,D_253,B_254] :
      ( r1_orders_2(A_252,D_253,'#skF_1'(A_252,B_254))
      | ~ r1_lattice3(A_252,B_254,D_253)
      | ~ m1_subset_1(D_253,u1_struct_0(A_252))
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_252)))
      | v1_xboole_0(B_254)
      | ~ v25_waybel_0(A_252)
      | ~ l1_orders_2(A_252)
      | ~ v3_orders_2(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_345,plain,(
    ! [D_253] :
      ( r1_orders_2('#skF_8',D_253,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9',D_253)
      | ~ m1_subset_1(D_253,u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | ~ v25_waybel_0('#skF_8')
      | ~ l1_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_280,c_341])).

tff(c_349,plain,(
    ! [D_253] :
      ( r1_orders_2('#skF_8',D_253,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9',D_253)
      | ~ m1_subset_1(D_253,u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_276,c_345])).

tff(c_351,plain,(
    ! [D_255] :
      ( r1_orders_2('#skF_8',D_255,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9',D_255)
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_275,c_349])).

tff(c_54,plain,(
    ! [C_104,B_102,A_98] :
      ( C_104 = B_102
      | ~ r1_orders_2(A_98,C_104,B_102)
      | ~ r1_orders_2(A_98,B_102,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_98))
      | ~ m1_subset_1(B_102,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_371,plain,(
    ! [D_255] :
      ( D_255 = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_255)
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8','#skF_9',D_255)
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_351,c_54])).

tff(c_390,plain,(
    ! [D_255] :
      ( D_255 = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_255)
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9',D_255)
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_371])).

tff(c_391,plain,(
    ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_405,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | v1_xboole_0('#skF_9')
    | ~ v25_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_391])).

tff(c_408,plain,
    ( v1_xboole_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_276,c_280,c_405])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_275,c_408])).

tff(c_412,plain,(
    m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_288,plain,(
    ! [A_203,B_204] :
      ( r1_lattice3(A_203,B_204,'#skF_1'(A_203,B_204))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | v1_xboole_0(B_204)
      | ~ v25_waybel_0(A_203)
      | ~ l1_orders_2(A_203)
      | ~ v3_orders_2(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_292,plain,
    ( r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | v1_xboole_0('#skF_9')
    | ~ v25_waybel_0('#skF_8')
    | ~ l1_orders_2('#skF_8')
    | ~ v3_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_280,c_288])).

tff(c_296,plain,
    ( r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | v1_xboole_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_276,c_292])).

tff(c_297,plain,(
    r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_275,c_296])).

tff(c_32,plain,(
    ! [A_27,B_65,C_84] :
      ( r1_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_27,B_65,C_84] :
      ( ~ r1_orders_2(A_27,'#skF_4'(A_27,B_65,C_84),C_84)
      | '#skF_5'(A_27,B_65,C_84) != C_84
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_361,plain,(
    ! [B_65] :
      ( '#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_351,c_30])).

tff(c_380,plain,(
    ! [B_65] :
      ( '#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_361])).

tff(c_581,plain,(
    ! [B_283] :
      ( '#skF_5'('#skF_8',B_283,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r2_yellow_0('#skF_8',B_283)
      | ~ r1_lattice3('#skF_8',B_283,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_283,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_283,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_380])).

tff(c_597,plain,(
    ! [B_65] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | '#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_581])).

tff(c_623,plain,(
    ! [B_287] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_287,'#skF_1'('#skF_8','#skF_9')))
      | '#skF_5'('#skF_8',B_287,'#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
      | r2_yellow_0('#skF_8',B_287)
      | ~ r1_lattice3('#skF_8',B_287,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_597])).

tff(c_635,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
    | r2_yellow_0('#skF_8','#skF_9')
    | ~ r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_623])).

tff(c_642,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9')
    | r2_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_297,c_635])).

tff(c_643,plain,(
    '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) != '#skF_1'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_642])).

tff(c_44,plain,(
    ! [A_27,B_65,C_84] :
      ( r1_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | r1_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [A_27,B_65,C_84] :
      ( ~ r1_orders_2(A_27,'#skF_4'(A_27,B_65,C_84),C_84)
      | r1_lattice3(A_27,B_65,'#skF_5'(A_27,B_65,C_84))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,(
    ! [B_65] :
      ( r1_lattice3('#skF_8',B_65,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_351,c_42])).

tff(c_377,plain,(
    ! [B_65] :
      ( r1_lattice3('#skF_8',B_65,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_357])).

tff(c_689,plain,(
    ! [B_296] :
      ( r1_lattice3('#skF_8',B_296,'#skF_5'('#skF_8',B_296,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_296)
      | ~ r1_lattice3('#skF_8',B_296,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_296,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_296,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_377])).

tff(c_698,plain,(
    ! [B_65] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_lattice3('#skF_8',B_65,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_46,c_689])).

tff(c_714,plain,(
    ! [B_297] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_297,'#skF_1'('#skF_8','#skF_9')))
      | r1_lattice3('#skF_8',B_297,'#skF_5'('#skF_8',B_297,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_297)
      | ~ r1_lattice3('#skF_8',B_297,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_698])).

tff(c_719,plain,
    ( r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r2_yellow_0('#skF_8','#skF_9')
    | ~ r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_714])).

tff(c_725,plain,
    ( r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r2_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_297,c_719])).

tff(c_726,plain,(
    r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_725])).

tff(c_50,plain,(
    ! [A_27,B_65,C_84] :
      ( r1_lattice3(A_27,B_65,'#skF_4'(A_27,B_65,C_84))
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_511,plain,(
    ! [A_272,B_273,C_274,E_275] :
      ( r1_lattice3(A_272,B_273,'#skF_4'(A_272,B_273,C_274))
      | r1_orders_2(A_272,E_275,'#skF_5'(A_272,B_273,C_274))
      | ~ r1_lattice3(A_272,B_273,E_275)
      | ~ m1_subset_1(E_275,u1_struct_0(A_272))
      | r2_yellow_0(A_272,B_273)
      | ~ r1_lattice3(A_272,B_273,C_274)
      | ~ m1_subset_1(C_274,u1_struct_0(A_272))
      | ~ l1_orders_2(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_411,plain,(
    ! [D_255] :
      ( D_255 = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_orders_2('#skF_8','#skF_1'('#skF_8','#skF_9'),D_255)
      | ~ r1_lattice3('#skF_8','#skF_9',D_255)
      | ~ m1_subset_1(D_255,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_518,plain,(
    ! [B_273,C_274] :
      ( '#skF_5'('#skF_8',B_273,C_274) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_273,C_274))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_273,C_274),u1_struct_0('#skF_8'))
      | r1_lattice3('#skF_8',B_273,'#skF_4'('#skF_8',B_273,C_274))
      | ~ r1_lattice3('#skF_8',B_273,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_273)
      | ~ r1_lattice3('#skF_8',B_273,C_274)
      | ~ m1_subset_1(C_274,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_511,c_411])).

tff(c_981,plain,(
    ! [B_313,C_314] :
      ( '#skF_5'('#skF_8',B_313,C_314) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_313,C_314))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_313,C_314),u1_struct_0('#skF_8'))
      | r1_lattice3('#skF_8',B_313,'#skF_4'('#skF_8',B_313,C_314))
      | ~ r1_lattice3('#skF_8',B_313,'#skF_1'('#skF_8','#skF_9'))
      | r2_yellow_0('#skF_8',B_313)
      | ~ r1_lattice3('#skF_8',B_313,C_314)
      | ~ m1_subset_1(C_314,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_518])).

tff(c_986,plain,(
    ! [B_65,C_84] :
      ( '#skF_5'('#skF_8',B_65,C_84) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_65,C_84))
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | r1_lattice3('#skF_8',B_65,'#skF_4'('#skF_8',B_65,C_84))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_981])).

tff(c_993,plain,(
    ! [B_315,C_316] :
      ( '#skF_5'('#skF_8',B_315,C_316) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_315,C_316))
      | ~ r1_lattice3('#skF_8',B_315,'#skF_1'('#skF_8','#skF_9'))
      | r1_lattice3('#skF_8',B_315,'#skF_4'('#skF_8',B_315,C_316))
      | r2_yellow_0('#skF_8',B_315)
      | ~ r1_lattice3('#skF_8',B_315,C_316)
      | ~ m1_subset_1(C_316,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_986])).

tff(c_995,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r2_yellow_0('#skF_8','#skF_9')
    | ~ r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_726,c_993])).

tff(c_999,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r2_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_297,c_995])).

tff(c_1000,plain,(
    r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_643,c_999])).

tff(c_52,plain,(
    ! [A_27,B_65,C_84] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_27,B_65,C_84] :
      ( ~ r1_orders_2(A_27,'#skF_4'(A_27,B_65,C_84),C_84)
      | m1_subset_1('#skF_5'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_354,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_351,c_48])).

tff(c_374,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_354])).

tff(c_652,plain,(
    ! [B_291] :
      ( m1_subset_1('#skF_5'('#skF_8',B_291,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_291)
      | ~ r1_lattice3('#skF_8',B_291,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_291,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_291,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_374])).

tff(c_660,plain,(
    ! [B_65] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_652])).

tff(c_674,plain,(
    ! [B_65] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | m1_subset_1('#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_660])).

tff(c_40,plain,(
    ! [A_27,B_65,C_84,E_90] :
      ( m1_subset_1('#skF_4'(A_27,B_65,C_84),u1_struct_0(A_27))
      | r1_orders_2(A_27,E_90,'#skF_5'(A_27,B_65,C_84))
      | ~ r1_lattice3(A_27,B_65,E_90)
      | ~ m1_subset_1(E_90,u1_struct_0(A_27))
      | r2_yellow_0(A_27,B_65)
      | ~ r1_lattice3(A_27,B_65,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_350,plain,(
    ! [D_253] :
      ( r1_orders_2('#skF_8',D_253,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9',D_253)
      | ~ m1_subset_1(D_253,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_275,c_349])).

tff(c_549,plain,(
    ! [A_276,B_277,C_278,E_279] :
      ( ~ r1_orders_2(A_276,'#skF_4'(A_276,B_277,C_278),C_278)
      | r1_orders_2(A_276,E_279,'#skF_5'(A_276,B_277,C_278))
      | ~ r1_lattice3(A_276,B_277,E_279)
      | ~ m1_subset_1(E_279,u1_struct_0(A_276))
      | r2_yellow_0(A_276,B_277)
      | ~ r1_lattice3(A_276,B_277,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(A_276))
      | ~ l1_orders_2(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_558,plain,(
    ! [E_279,B_277] :
      ( r1_orders_2('#skF_8',E_279,'#skF_5'('#skF_8',B_277,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_277,E_279)
      | ~ m1_subset_1(E_279,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_277)
      | ~ r1_lattice3('#skF_8',B_277,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_277,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_277,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_350,c_549])).

tff(c_748,plain,(
    ! [E_301,B_302] :
      ( r1_orders_2('#skF_8',E_301,'#skF_5'('#skF_8',B_302,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_302,E_301)
      | ~ m1_subset_1(E_301,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_302)
      | ~ r1_lattice3('#skF_8',B_302,'#skF_1'('#skF_8','#skF_9'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_302,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_4'('#skF_8',B_302,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_558])).

tff(c_751,plain,(
    ! [E_301,B_65,E_90] :
      ( r1_orders_2('#skF_8',E_301,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_65,E_301)
      | ~ m1_subset_1(E_301,u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_orders_2('#skF_8',E_90,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_65,E_90)
      | ~ m1_subset_1(E_90,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_748])).

tff(c_763,plain,(
    ! [E_301,B_65,E_90] :
      ( r1_orders_2('#skF_8',E_301,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_65,E_301)
      | ~ m1_subset_1(E_301,u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | r1_orders_2('#skF_8',E_90,'#skF_5'('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_65,E_90)
      | ~ m1_subset_1(E_90,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_65)
      | ~ r1_lattice3('#skF_8',B_65,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_412,c_751])).

tff(c_904,plain,(
    ! [B_306,E_307] :
      ( ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8',B_306,E_307)
      | ~ m1_subset_1(E_307,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_306)
      | ~ r1_lattice3('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9'))
      | r1_orders_2('#skF_8',E_307,'#skF_5'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9'))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_763])).

tff(c_914,plain,(
    ! [B_306] :
      ( '#skF_5'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',B_306)
      | ~ r1_lattice3('#skF_8',B_306,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_904,c_411])).

tff(c_1014,plain,(
    ! [B_317] :
      ( '#skF_5'('#skF_8',B_317,'#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_317,'#skF_1'('#skF_8','#skF_9')))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_317,'#skF_1'('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_317,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_317)
      | ~ r1_lattice3('#skF_8',B_317,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_914])).

tff(c_1026,plain,(
    ! [B_318] :
      ( '#skF_5'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')))
      | ~ r1_lattice3('#skF_8','#skF_9','#skF_4'('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')))
      | r2_yellow_0('#skF_8',B_318)
      | ~ r1_lattice3('#skF_8',B_318,'#skF_1'('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_674,c_1014])).

tff(c_1029,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | ~ r1_lattice3('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')))
    | r2_yellow_0('#skF_8','#skF_9')
    | ~ r1_lattice3('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_1000,c_1026])).

tff(c_1044,plain,
    ( '#skF_5'('#skF_8','#skF_9','#skF_1'('#skF_8','#skF_9')) = '#skF_1'('#skF_8','#skF_9')
    | r2_yellow_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_726,c_1029])).

tff(c_1046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_643,c_1044])).

%------------------------------------------------------------------------------
