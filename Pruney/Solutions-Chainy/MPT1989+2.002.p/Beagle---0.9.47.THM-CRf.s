%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 515 expanded)
%              Number of leaves         :   42 ( 210 expanded)
%              Depth                    :   21
%              Number of atoms          :  400 (2572 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_waybel_7,type,(
    v4_waybel_7: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_215,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v5_waybel_6(B,A)
             => v4_waybel_7(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_7)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_195,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
           => v1_waybel_7(k5_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_58,axiom,(
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

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_176,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v4_waybel_7(B,A)
          <=> ? [C] :
                ( ~ v1_xboole_0(C)
                & v1_waybel_0(C,A)
                & v12_waybel_0(C,A)
                & v1_waybel_7(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                & B = k1_yellow_0(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_7)).

tff(c_66,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_70,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_76,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_92,plain,(
    ! [A_75,B_76] :
      ( r1_orders_2(A_75,B_76,B_76)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_100,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_96])).

tff(c_101,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_104])).

tff(c_110,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_74,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_34,plain,(
    ! [A_43,B_44] :
      ( v12_waybel_0(k5_waybel_0(A_43,B_44),A_43)
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_72,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_68,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_62,plain,(
    v5_waybel_6('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_58,plain,(
    ! [A_64,B_66] :
      ( v1_waybel_7(k5_waybel_0(A_64,B_66),A_64)
      | ~ v5_waybel_6(B_66,A_64)
      | ~ m1_subset_1(B_66,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64)
      | ~ v2_lattice3(A_64)
      | ~ v1_lattice3(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_36,plain,(
    ! [A_45,B_46] :
      ( v1_waybel_0(k5_waybel_0(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_79,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(k5_waybel_0(A_71,B_72))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_89,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_85])).

tff(c_90,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_60,plain,(
    ~ v4_waybel_7('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_109,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_12,plain,(
    ! [A_5,B_12,C_13] :
      ( m1_subset_1('#skF_1'(A_5,B_12,C_13),u1_struct_0(A_5))
      | r2_lattice3(A_5,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_5,B_12,C_13] :
      ( r2_hidden('#skF_1'(A_5,B_12,C_13),B_12)
      | r2_lattice3(A_5,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_orders_2(A_101,C_102,B_103)
      | ~ r2_hidden(C_102,k5_waybel_0(A_101,B_103))
      | ~ m1_subset_1(C_102,u1_struct_0(A_101))
      | ~ m1_subset_1(B_103,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_380,plain,(
    ! [A_206,A_207,B_208,C_209] :
      ( r1_orders_2(A_206,'#skF_1'(A_207,k5_waybel_0(A_206,B_208),C_209),B_208)
      | ~ m1_subset_1('#skF_1'(A_207,k5_waybel_0(A_206,B_208),C_209),u1_struct_0(A_206))
      | ~ m1_subset_1(B_208,u1_struct_0(A_206))
      | ~ l1_orders_2(A_206)
      | v2_struct_0(A_206)
      | r2_lattice3(A_207,k5_waybel_0(A_206,B_208),C_209)
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_400,plain,(
    ! [A_213,B_214,C_215] :
      ( r1_orders_2(A_213,'#skF_1'(A_213,k5_waybel_0(A_213,B_214),C_215),B_214)
      | ~ m1_subset_1(B_214,u1_struct_0(A_213))
      | v2_struct_0(A_213)
      | r2_lattice3(A_213,k5_waybel_0(A_213,B_214),C_215)
      | ~ m1_subset_1(C_215,u1_struct_0(A_213))
      | ~ l1_orders_2(A_213) ) ),
    inference(resolution,[status(thm)],[c_12,c_380])).

tff(c_8,plain,(
    ! [A_5,B_12,C_13] :
      ( ~ r1_orders_2(A_5,'#skF_1'(A_5,B_12,C_13),C_13)
      | r2_lattice3(A_5,B_12,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_405,plain,(
    ! [A_213,B_214] :
      ( v2_struct_0(A_213)
      | r2_lattice3(A_213,k5_waybel_0(A_213,B_214),B_214)
      | ~ m1_subset_1(B_214,u1_struct_0(A_213))
      | ~ l1_orders_2(A_213) ) ),
    inference(resolution,[status(thm)],[c_400,c_8])).

tff(c_30,plain,(
    ! [A_19,B_31,C_37] :
      ( m1_subset_1('#skF_2'(A_19,B_31,C_37),u1_struct_0(A_19))
      | k1_yellow_0(A_19,C_37) = B_31
      | ~ r2_lattice3(A_19,C_37,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [A_19,C_37,B_31] :
      ( r2_lattice3(A_19,C_37,'#skF_2'(A_19,B_31,C_37))
      | k1_yellow_0(A_19,C_37) = B_31
      | ~ r2_lattice3(A_19,C_37,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [C_53,A_47,B_51] :
      ( r2_hidden(C_53,k5_waybel_0(A_47,B_51))
      | ~ r1_orders_2(A_47,C_53,B_51)
      | ~ m1_subset_1(C_53,u1_struct_0(A_47))
      | ~ m1_subset_1(B_51,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_141,plain,(
    ! [A_104,D_105,C_106,B_107] :
      ( r1_orders_2(A_104,D_105,C_106)
      | ~ r2_hidden(D_105,B_107)
      | ~ m1_subset_1(D_105,u1_struct_0(A_104))
      | ~ r2_lattice3(A_104,B_107,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_330,plain,(
    ! [C_190,B_191,A_188,A_189,C_192] :
      ( r1_orders_2(A_189,C_190,C_192)
      | ~ m1_subset_1(C_190,u1_struct_0(A_189))
      | ~ r2_lattice3(A_189,k5_waybel_0(A_188,B_191),C_192)
      | ~ m1_subset_1(C_192,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ r1_orders_2(A_188,C_190,B_191)
      | ~ m1_subset_1(C_190,u1_struct_0(A_188))
      | ~ m1_subset_1(B_191,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_340,plain,(
    ! [C_192,A_188,B_191] :
      ( r1_orders_2('#skF_4','#skF_5',C_192)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_188,B_191),C_192)
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2(A_188,'#skF_5',B_191)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_188))
      | ~ m1_subset_1(B_191,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_64,c_330])).

tff(c_348,plain,(
    ! [C_193,A_194,B_195] :
      ( r1_orders_2('#skF_4','#skF_5',C_193)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_194,B_195),C_193)
      | ~ m1_subset_1(C_193,u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_194,'#skF_5',B_195)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_194))
      | ~ m1_subset_1(B_195,u1_struct_0(A_194))
      | ~ l1_orders_2(A_194)
      | v2_struct_0(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_340])).

tff(c_352,plain,(
    ! [B_31,A_194,B_195] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_31,k5_waybel_0(A_194,B_195)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_31,k5_waybel_0(A_194,B_195)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_194,'#skF_5',B_195)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_194))
      | ~ m1_subset_1(B_195,u1_struct_0(A_194))
      | ~ l1_orders_2(A_194)
      | v2_struct_0(A_194)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_194,B_195)) = B_31
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_194,B_195),B_31)
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_348])).

tff(c_742,plain,(
    ! [B_260,A_261,B_262] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_260,k5_waybel_0(A_261,B_262)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_260,k5_waybel_0(A_261,B_262)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_261,'#skF_5',B_262)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_261))
      | ~ m1_subset_1(B_262,u1_struct_0(A_261))
      | ~ l1_orders_2(A_261)
      | v2_struct_0(A_261)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_261,B_262)) = B_260
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_261,B_262),B_260)
      | ~ m1_subset_1(B_260,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_352])).

tff(c_746,plain,(
    ! [B_31,A_261,B_262] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_31,k5_waybel_0(A_261,B_262)))
      | ~ r1_orders_2(A_261,'#skF_5',B_262)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_261))
      | ~ m1_subset_1(B_262,u1_struct_0(A_261))
      | ~ l1_orders_2(A_261)
      | v2_struct_0(A_261)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_261,B_262)) = B_31
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_261,B_262),B_31)
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_742])).

tff(c_757,plain,(
    ! [B_263,A_264,B_265] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_263,k5_waybel_0(A_264,B_265)))
      | ~ r1_orders_2(A_264,'#skF_5',B_265)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_264))
      | ~ m1_subset_1(B_265,u1_struct_0(A_264))
      | ~ l1_orders_2(A_264)
      | v2_struct_0(A_264)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_264,B_265)) = B_263
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_264,B_265),B_263)
      | ~ m1_subset_1(B_263,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_746])).

tff(c_26,plain,(
    ! [A_19,B_31,C_37] :
      ( ~ r1_orders_2(A_19,B_31,'#skF_2'(A_19,B_31,C_37))
      | k1_yellow_0(A_19,C_37) = B_31
      | ~ r2_lattice3(A_19,C_37,B_31)
      | ~ m1_subset_1(B_31,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19)
      | ~ v5_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_761,plain,(
    ! [A_264,B_265] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_orders_2(A_264,'#skF_5',B_265)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_264))
      | ~ m1_subset_1(B_265,u1_struct_0(A_264))
      | ~ l1_orders_2(A_264)
      | v2_struct_0(A_264)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_264,B_265)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_264,B_265),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_757,c_26])).

tff(c_772,plain,(
    ! [A_266,B_267] :
      ( ~ r1_orders_2(A_266,'#skF_5',B_267)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_266))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266)
      | v2_struct_0(A_266)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_266,B_267)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_266,B_267),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72,c_66,c_761])).

tff(c_776,plain,
    ( ~ r1_orders_2('#skF_4','#skF_5','#skF_5')
    | k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_405,c_772])).

tff(c_779,plain,
    ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_109,c_776])).

tff(c_780,plain,(
    k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_779])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k5_waybel_0(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_yellow_0(A_17,B_18),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_274,plain,(
    ! [A_168,C_169] :
      ( v4_waybel_7(k1_yellow_0(A_168,C_169),A_168)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ v1_waybel_7(C_169,A_168)
      | ~ v12_waybel_0(C_169,A_168)
      | ~ v1_waybel_0(C_169,A_168)
      | v1_xboole_0(C_169)
      | ~ m1_subset_1(k1_yellow_0(A_168,C_169),u1_struct_0(A_168))
      | ~ l1_orders_2(A_168)
      | ~ v2_lattice3(A_168)
      | ~ v1_lattice3(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_283,plain,(
    ! [A_173,B_174] :
      ( v4_waybel_7(k1_yellow_0(A_173,B_174),A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ v1_waybel_7(B_174,A_173)
      | ~ v12_waybel_0(B_174,A_173)
      | ~ v1_waybel_0(B_174,A_173)
      | v1_xboole_0(B_174)
      | ~ v2_lattice3(A_173)
      | ~ v1_lattice3(A_173)
      | ~ v5_orders_2(A_173)
      | ~ v4_orders_2(A_173)
      | ~ v3_orders_2(A_173)
      | ~ l1_orders_2(A_173) ) ),
    inference(resolution,[status(thm)],[c_14,c_274])).

tff(c_289,plain,(
    ! [A_41,B_42] :
      ( v4_waybel_7(k1_yellow_0(A_41,k5_waybel_0(A_41,B_42)),A_41)
      | ~ v1_waybel_7(k5_waybel_0(A_41,B_42),A_41)
      | ~ v12_waybel_0(k5_waybel_0(A_41,B_42),A_41)
      | ~ v1_waybel_0(k5_waybel_0(A_41,B_42),A_41)
      | v1_xboole_0(k5_waybel_0(A_41,B_42))
      | ~ v2_lattice3(A_41)
      | ~ v1_lattice3(A_41)
      | ~ v5_orders_2(A_41)
      | ~ v4_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_283])).

tff(c_793,plain,
    ( v4_waybel_7('#skF_5','#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_289])).

tff(c_852,plain,
    ( v4_waybel_7('#skF_5','#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_76,c_74,c_72,c_70,c_68,c_793])).

tff(c_853,plain,
    ( ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_90,c_60,c_852])).

tff(c_982,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_985,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_982])).

tff(c_988,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_64,c_985])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_988])).

tff(c_991,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_993,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_996,plain,
    ( ~ v5_waybel_6('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_993])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_62,c_996])).

tff(c_1001,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_1005,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1001])).

tff(c_1008,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_64,c_1005])).

tff(c_1010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1008])).

tff(c_1011,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1015,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_1011,c_4])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_1015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.69  
% 4.28/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.70  %$ r2_lattice3 > r1_orders_2 > v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.28/1.70  
% 4.28/1.70  %Foreground sorts:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Background operators:
% 4.28/1.70  
% 4.28/1.70  
% 4.28/1.70  %Foreground operators:
% 4.28/1.70  tff(v1_waybel_7, type, v1_waybel_7: ($i * $i) > $o).
% 4.28/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.28/1.70  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 4.28/1.70  tff(v5_waybel_6, type, v5_waybel_6: ($i * $i) > $o).
% 4.28/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.28/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.70  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.28/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.28/1.70  tff(v12_waybel_0, type, v12_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.28/1.70  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 4.28/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.70  tff(v4_waybel_7, type, v4_waybel_7: ($i * $i) > $o).
% 4.28/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.28/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.28/1.70  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 4.28/1.70  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 4.28/1.70  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.28/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.28/1.70  tff(v1_waybel_0, type, v1_waybel_0: ($i * $i) > $o).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.70  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.28/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.28/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.28/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.70  
% 4.28/1.72  tff(f_215, negated_conjecture, ~(![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v4_waybel_7(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_waybel_7)).
% 4.28/1.72  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 4.28/1.72  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 4.28/1.72  tff(f_116, axiom, (![A, B]: ((((~v2_struct_0(A) & v4_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => v12_waybel_0(k5_waybel_0(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_waybel_0)).
% 4.28/1.72  tff(f_195, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v1_waybel_7(k5_waybel_0(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_waybel_7)).
% 4.28/1.72  tff(f_130, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k5_waybel_0(A, B)) & v1_waybel_0(k5_waybel_0(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_waybel_0)).
% 4.28/1.72  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 4.28/1.72  tff(f_145, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k5_waybel_0(A, B)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_waybel_0)).
% 4.28/1.72  tff(f_96, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 4.28/1.72  tff(f_105, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k5_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 4.28/1.72  tff(f_62, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 4.28/1.72  tff(f_176, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v4_waybel_7(B, A) <=> (?[C]: (((((~v1_xboole_0(C) & v1_waybel_0(C, A)) & v12_waybel_0(C, A)) & v1_waybel_7(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) & (B = k1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_waybel_7)).
% 4.28/1.72  tff(c_66, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_70, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_76, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_92, plain, (![A_75, B_76]: (r1_orders_2(A_75, B_76, B_76) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.72  tff(c_96, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_92])).
% 4.28/1.72  tff(c_100, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_96])).
% 4.28/1.72  tff(c_101, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 4.28/1.72  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.72  tff(c_104, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_101, c_4])).
% 4.28/1.72  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_104])).
% 4.28/1.72  tff(c_110, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 4.28/1.72  tff(c_74, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_34, plain, (![A_43, B_44]: (v12_waybel_0(k5_waybel_0(A_43, B_44), A_43) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_orders_2(A_43) | ~v4_orders_2(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.28/1.72  tff(c_72, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_68, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_62, plain, (v5_waybel_6('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_58, plain, (![A_64, B_66]: (v1_waybel_7(k5_waybel_0(A_64, B_66), A_64) | ~v5_waybel_6(B_66, A_64) | ~m1_subset_1(B_66, u1_struct_0(A_64)) | ~l1_orders_2(A_64) | ~v2_lattice3(A_64) | ~v1_lattice3(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.28/1.72  tff(c_36, plain, (![A_45, B_46]: (v1_waybel_0(k5_waybel_0(A_45, B_46), A_45) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.28/1.72  tff(c_79, plain, (![A_71, B_72]: (~v1_xboole_0(k5_waybel_0(A_71, B_72)) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.28/1.72  tff(c_85, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_79])).
% 4.28/1.72  tff(c_89, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_85])).
% 4.28/1.72  tff(c_90, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_89])).
% 4.28/1.72  tff(c_60, plain, (~v4_waybel_7('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.28/1.72  tff(c_109, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 4.28/1.72  tff(c_12, plain, (![A_5, B_12, C_13]: (m1_subset_1('#skF_1'(A_5, B_12, C_13), u1_struct_0(A_5)) | r2_lattice3(A_5, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.72  tff(c_10, plain, (![A_5, B_12, C_13]: (r2_hidden('#skF_1'(A_5, B_12, C_13), B_12) | r2_lattice3(A_5, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.72  tff(c_131, plain, (![A_101, C_102, B_103]: (r1_orders_2(A_101, C_102, B_103) | ~r2_hidden(C_102, k5_waybel_0(A_101, B_103)) | ~m1_subset_1(C_102, u1_struct_0(A_101)) | ~m1_subset_1(B_103, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.28/1.72  tff(c_380, plain, (![A_206, A_207, B_208, C_209]: (r1_orders_2(A_206, '#skF_1'(A_207, k5_waybel_0(A_206, B_208), C_209), B_208) | ~m1_subset_1('#skF_1'(A_207, k5_waybel_0(A_206, B_208), C_209), u1_struct_0(A_206)) | ~m1_subset_1(B_208, u1_struct_0(A_206)) | ~l1_orders_2(A_206) | v2_struct_0(A_206) | r2_lattice3(A_207, k5_waybel_0(A_206, B_208), C_209) | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~l1_orders_2(A_207))), inference(resolution, [status(thm)], [c_10, c_131])).
% 4.28/1.72  tff(c_400, plain, (![A_213, B_214, C_215]: (r1_orders_2(A_213, '#skF_1'(A_213, k5_waybel_0(A_213, B_214), C_215), B_214) | ~m1_subset_1(B_214, u1_struct_0(A_213)) | v2_struct_0(A_213) | r2_lattice3(A_213, k5_waybel_0(A_213, B_214), C_215) | ~m1_subset_1(C_215, u1_struct_0(A_213)) | ~l1_orders_2(A_213))), inference(resolution, [status(thm)], [c_12, c_380])).
% 4.28/1.72  tff(c_8, plain, (![A_5, B_12, C_13]: (~r1_orders_2(A_5, '#skF_1'(A_5, B_12, C_13), C_13) | r2_lattice3(A_5, B_12, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_5)) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.72  tff(c_405, plain, (![A_213, B_214]: (v2_struct_0(A_213) | r2_lattice3(A_213, k5_waybel_0(A_213, B_214), B_214) | ~m1_subset_1(B_214, u1_struct_0(A_213)) | ~l1_orders_2(A_213))), inference(resolution, [status(thm)], [c_400, c_8])).
% 4.28/1.72  tff(c_30, plain, (![A_19, B_31, C_37]: (m1_subset_1('#skF_2'(A_19, B_31, C_37), u1_struct_0(A_19)) | k1_yellow_0(A_19, C_37)=B_31 | ~r2_lattice3(A_19, C_37, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_19)) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.28/1.72  tff(c_28, plain, (![A_19, C_37, B_31]: (r2_lattice3(A_19, C_37, '#skF_2'(A_19, B_31, C_37)) | k1_yellow_0(A_19, C_37)=B_31 | ~r2_lattice3(A_19, C_37, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_19)) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.28/1.72  tff(c_40, plain, (![C_53, A_47, B_51]: (r2_hidden(C_53, k5_waybel_0(A_47, B_51)) | ~r1_orders_2(A_47, C_53, B_51) | ~m1_subset_1(C_53, u1_struct_0(A_47)) | ~m1_subset_1(B_51, u1_struct_0(A_47)) | ~l1_orders_2(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.28/1.72  tff(c_141, plain, (![A_104, D_105, C_106, B_107]: (r1_orders_2(A_104, D_105, C_106) | ~r2_hidden(D_105, B_107) | ~m1_subset_1(D_105, u1_struct_0(A_104)) | ~r2_lattice3(A_104, B_107, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.72  tff(c_330, plain, (![C_190, B_191, A_188, A_189, C_192]: (r1_orders_2(A_189, C_190, C_192) | ~m1_subset_1(C_190, u1_struct_0(A_189)) | ~r2_lattice3(A_189, k5_waybel_0(A_188, B_191), C_192) | ~m1_subset_1(C_192, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~r1_orders_2(A_188, C_190, B_191) | ~m1_subset_1(C_190, u1_struct_0(A_188)) | ~m1_subset_1(B_191, u1_struct_0(A_188)) | ~l1_orders_2(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_40, c_141])).
% 4.28/1.72  tff(c_340, plain, (![C_192, A_188, B_191]: (r1_orders_2('#skF_4', '#skF_5', C_192) | ~r2_lattice3('#skF_4', k5_waybel_0(A_188, B_191), C_192) | ~m1_subset_1(C_192, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r1_orders_2(A_188, '#skF_5', B_191) | ~m1_subset_1('#skF_5', u1_struct_0(A_188)) | ~m1_subset_1(B_191, u1_struct_0(A_188)) | ~l1_orders_2(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_64, c_330])).
% 4.28/1.72  tff(c_348, plain, (![C_193, A_194, B_195]: (r1_orders_2('#skF_4', '#skF_5', C_193) | ~r2_lattice3('#skF_4', k5_waybel_0(A_194, B_195), C_193) | ~m1_subset_1(C_193, u1_struct_0('#skF_4')) | ~r1_orders_2(A_194, '#skF_5', B_195) | ~m1_subset_1('#skF_5', u1_struct_0(A_194)) | ~m1_subset_1(B_195, u1_struct_0(A_194)) | ~l1_orders_2(A_194) | v2_struct_0(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_340])).
% 4.28/1.72  tff(c_352, plain, (![B_31, A_194, B_195]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_31, k5_waybel_0(A_194, B_195))) | ~m1_subset_1('#skF_2'('#skF_4', B_31, k5_waybel_0(A_194, B_195)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_194, '#skF_5', B_195) | ~m1_subset_1('#skF_5', u1_struct_0(A_194)) | ~m1_subset_1(B_195, u1_struct_0(A_194)) | ~l1_orders_2(A_194) | v2_struct_0(A_194) | k1_yellow_0('#skF_4', k5_waybel_0(A_194, B_195))=B_31 | ~r2_lattice3('#skF_4', k5_waybel_0(A_194, B_195), B_31) | ~m1_subset_1(B_31, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_348])).
% 4.28/1.72  tff(c_742, plain, (![B_260, A_261, B_262]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_260, k5_waybel_0(A_261, B_262))) | ~m1_subset_1('#skF_2'('#skF_4', B_260, k5_waybel_0(A_261, B_262)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_261, '#skF_5', B_262) | ~m1_subset_1('#skF_5', u1_struct_0(A_261)) | ~m1_subset_1(B_262, u1_struct_0(A_261)) | ~l1_orders_2(A_261) | v2_struct_0(A_261) | k1_yellow_0('#skF_4', k5_waybel_0(A_261, B_262))=B_260 | ~r2_lattice3('#skF_4', k5_waybel_0(A_261, B_262), B_260) | ~m1_subset_1(B_260, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_352])).
% 4.28/1.72  tff(c_746, plain, (![B_31, A_261, B_262]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_31, k5_waybel_0(A_261, B_262))) | ~r1_orders_2(A_261, '#skF_5', B_262) | ~m1_subset_1('#skF_5', u1_struct_0(A_261)) | ~m1_subset_1(B_262, u1_struct_0(A_261)) | ~l1_orders_2(A_261) | v2_struct_0(A_261) | k1_yellow_0('#skF_4', k5_waybel_0(A_261, B_262))=B_31 | ~r2_lattice3('#skF_4', k5_waybel_0(A_261, B_262), B_31) | ~m1_subset_1(B_31, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_742])).
% 4.28/1.72  tff(c_757, plain, (![B_263, A_264, B_265]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_263, k5_waybel_0(A_264, B_265))) | ~r1_orders_2(A_264, '#skF_5', B_265) | ~m1_subset_1('#skF_5', u1_struct_0(A_264)) | ~m1_subset_1(B_265, u1_struct_0(A_264)) | ~l1_orders_2(A_264) | v2_struct_0(A_264) | k1_yellow_0('#skF_4', k5_waybel_0(A_264, B_265))=B_263 | ~r2_lattice3('#skF_4', k5_waybel_0(A_264, B_265), B_263) | ~m1_subset_1(B_263, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_746])).
% 4.28/1.72  tff(c_26, plain, (![A_19, B_31, C_37]: (~r1_orders_2(A_19, B_31, '#skF_2'(A_19, B_31, C_37)) | k1_yellow_0(A_19, C_37)=B_31 | ~r2_lattice3(A_19, C_37, B_31) | ~m1_subset_1(B_31, u1_struct_0(A_19)) | ~l1_orders_2(A_19) | ~v5_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.28/1.72  tff(c_761, plain, (![A_264, B_265]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r1_orders_2(A_264, '#skF_5', B_265) | ~m1_subset_1('#skF_5', u1_struct_0(A_264)) | ~m1_subset_1(B_265, u1_struct_0(A_264)) | ~l1_orders_2(A_264) | v2_struct_0(A_264) | k1_yellow_0('#skF_4', k5_waybel_0(A_264, B_265))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_264, B_265), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_757, c_26])).
% 4.28/1.72  tff(c_772, plain, (![A_266, B_267]: (~r1_orders_2(A_266, '#skF_5', B_267) | ~m1_subset_1('#skF_5', u1_struct_0(A_266)) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l1_orders_2(A_266) | v2_struct_0(A_266) | k1_yellow_0('#skF_4', k5_waybel_0(A_266, B_267))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_266, B_267), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72, c_66, c_761])).
% 4.28/1.72  tff(c_776, plain, (~r1_orders_2('#skF_4', '#skF_5', '#skF_5') | k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_405, c_772])).
% 4.28/1.72  tff(c_779, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_109, c_776])).
% 4.28/1.72  tff(c_780, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_110, c_779])).
% 4.28/1.72  tff(c_32, plain, (![A_41, B_42]: (m1_subset_1(k5_waybel_0(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.28/1.72  tff(c_14, plain, (![A_17, B_18]: (m1_subset_1(k1_yellow_0(A_17, B_18), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.28/1.72  tff(c_274, plain, (![A_168, C_169]: (v4_waybel_7(k1_yellow_0(A_168, C_169), A_168) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~v1_waybel_7(C_169, A_168) | ~v12_waybel_0(C_169, A_168) | ~v1_waybel_0(C_169, A_168) | v1_xboole_0(C_169) | ~m1_subset_1(k1_yellow_0(A_168, C_169), u1_struct_0(A_168)) | ~l1_orders_2(A_168) | ~v2_lattice3(A_168) | ~v1_lattice3(A_168) | ~v5_orders_2(A_168) | ~v4_orders_2(A_168) | ~v3_orders_2(A_168))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.28/1.72  tff(c_283, plain, (![A_173, B_174]: (v4_waybel_7(k1_yellow_0(A_173, B_174), A_173) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~v1_waybel_7(B_174, A_173) | ~v12_waybel_0(B_174, A_173) | ~v1_waybel_0(B_174, A_173) | v1_xboole_0(B_174) | ~v2_lattice3(A_173) | ~v1_lattice3(A_173) | ~v5_orders_2(A_173) | ~v4_orders_2(A_173) | ~v3_orders_2(A_173) | ~l1_orders_2(A_173))), inference(resolution, [status(thm)], [c_14, c_274])).
% 4.28/1.72  tff(c_289, plain, (![A_41, B_42]: (v4_waybel_7(k1_yellow_0(A_41, k5_waybel_0(A_41, B_42)), A_41) | ~v1_waybel_7(k5_waybel_0(A_41, B_42), A_41) | ~v12_waybel_0(k5_waybel_0(A_41, B_42), A_41) | ~v1_waybel_0(k5_waybel_0(A_41, B_42), A_41) | v1_xboole_0(k5_waybel_0(A_41, B_42)) | ~v2_lattice3(A_41) | ~v1_lattice3(A_41) | ~v5_orders_2(A_41) | ~v4_orders_2(A_41) | ~v3_orders_2(A_41) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_32, c_283])).
% 4.28/1.72  tff(c_793, plain, (v4_waybel_7('#skF_5', '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_780, c_289])).
% 4.28/1.72  tff(c_852, plain, (v4_waybel_7('#skF_5', '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_76, c_74, c_72, c_70, c_68, c_793])).
% 4.28/1.72  tff(c_853, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_110, c_90, c_60, c_852])).
% 4.28/1.72  tff(c_982, plain, (~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_853])).
% 4.28/1.72  tff(c_985, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_982])).
% 4.28/1.72  tff(c_988, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_64, c_985])).
% 4.28/1.72  tff(c_990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_988])).
% 4.28/1.72  tff(c_991, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_853])).
% 4.28/1.72  tff(c_993, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_991])).
% 4.28/1.72  tff(c_996, plain, (~v5_waybel_6('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_58, c_993])).
% 4.28/1.72  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_62, c_996])).
% 4.28/1.72  tff(c_1001, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_991])).
% 4.28/1.72  tff(c_1005, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1001])).
% 4.28/1.72  tff(c_1008, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_64, c_1005])).
% 4.28/1.72  tff(c_1010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1008])).
% 4.28/1.72  tff(c_1011, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_89])).
% 4.28/1.72  tff(c_1015, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_1011, c_4])).
% 4.28/1.72  tff(c_1019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_1015])).
% 4.28/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.72  
% 4.28/1.72  Inference rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Ref     : 0
% 4.28/1.72  #Sup     : 207
% 4.28/1.72  #Fact    : 0
% 4.28/1.72  #Define  : 0
% 4.28/1.72  #Split   : 4
% 4.28/1.72  #Chain   : 0
% 4.28/1.72  #Close   : 0
% 4.28/1.72  
% 4.28/1.72  Ordering : KBO
% 4.28/1.72  
% 4.28/1.72  Simplification rules
% 4.28/1.72  ----------------------
% 4.28/1.72  #Subsume      : 47
% 4.28/1.72  #Demod        : 262
% 4.28/1.72  #Tautology    : 44
% 4.28/1.72  #SimpNegUnit  : 20
% 4.28/1.72  #BackRed      : 0
% 4.28/1.72  
% 4.28/1.72  #Partial instantiations: 0
% 4.28/1.72  #Strategies tried      : 1
% 4.28/1.72  
% 4.28/1.72  Timing (in seconds)
% 4.28/1.72  ----------------------
% 4.28/1.72  Preprocessing        : 0.35
% 4.28/1.72  Parsing              : 0.19
% 4.28/1.73  CNF conversion       : 0.03
% 4.28/1.73  Main loop            : 0.61
% 4.28/1.73  Inferencing          : 0.25
% 4.28/1.73  Reduction            : 0.16
% 4.28/1.73  Demodulation         : 0.11
% 4.28/1.73  BG Simplification    : 0.03
% 4.28/1.73  Subsumption          : 0.13
% 4.28/1.73  Abstraction          : 0.03
% 4.28/1.73  MUC search           : 0.00
% 4.28/1.73  Cooper               : 0.00
% 4.28/1.73  Total                : 1.00
% 4.28/1.73  Index Insertion      : 0.00
% 4.28/1.73  Index Deletion       : 0.00
% 4.28/1.73  Index Matching       : 0.00
% 4.28/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
