%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:05 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 905 expanded)
%              Number of leaves         :   41 ( 352 expanded)
%              Depth                    :   22
%              Number of atoms          :  381 (4816 expanded)
%              Number of equality atoms :   15 ( 148 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

tff(f_217,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

tff(f_197,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_178,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

tff(c_66,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_70,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_76,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_74,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_72,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_68,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_62,plain,(
    v5_waybel_6('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_58,plain,(
    ! [A_65,B_67] :
      ( v1_waybel_7(k5_waybel_0(A_65,B_67),A_65)
      | ~ v5_waybel_6(B_67,A_65)
      | ~ m1_subset_1(B_67,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65)
      | ~ v2_lattice3(A_65)
      | ~ v1_lattice3(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_87,plain,(
    ! [A_75,B_76] :
      ( r1_orders_2(A_75,B_76,B_76)
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_92,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_89])).

tff(c_94,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_6])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_97])).

tff(c_103,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_34,plain,(
    ! [A_44,B_45] :
      ( v12_waybel_0(k5_waybel_0(A_44,B_45),A_44)
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k5_waybel_0(A_42,B_43),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( v1_waybel_0(k5_waybel_0(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_79,plain,(
    ! [A_73,B_74] :
      ( ~ v1_xboole_0(k5_waybel_0(A_73,B_74))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_82,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_82])).

tff(c_86,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_60,plain,(
    ~ v4_waybel_7('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_102,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_14,plain,(
    ! [A_8,B_15,C_16] :
      ( m1_subset_1('#skF_1'(A_8,B_15,C_16),u1_struct_0(A_8))
      | r2_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_8,B_15,C_16] :
      ( r2_hidden('#skF_1'(A_8,B_15,C_16),B_15)
      | r2_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_orders_2(A_104,C_105,B_106)
      | ~ r2_hidden(C_105,k5_waybel_0(A_104,B_106))
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ m1_subset_1(B_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_331,plain,(
    ! [A_209,A_210,B_211,C_212] :
      ( r1_orders_2(A_209,'#skF_1'(A_210,k5_waybel_0(A_209,B_211),C_212),B_211)
      | ~ m1_subset_1('#skF_1'(A_210,k5_waybel_0(A_209,B_211),C_212),u1_struct_0(A_209))
      | ~ m1_subset_1(B_211,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | v2_struct_0(A_209)
      | r2_lattice3(A_210,k5_waybel_0(A_209,B_211),C_212)
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ l1_orders_2(A_210) ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_355,plain,(
    ! [A_216,B_217,C_218] :
      ( r1_orders_2(A_216,'#skF_1'(A_216,k5_waybel_0(A_216,B_217),C_218),B_217)
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | v2_struct_0(A_216)
      | r2_lattice3(A_216,k5_waybel_0(A_216,B_217),C_218)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216) ) ),
    inference(resolution,[status(thm)],[c_14,c_331])).

tff(c_10,plain,(
    ! [A_8,B_15,C_16] :
      ( ~ r1_orders_2(A_8,'#skF_1'(A_8,B_15,C_16),C_16)
      | r2_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_360,plain,(
    ! [A_216,B_217] :
      ( v2_struct_0(A_216)
      | r2_lattice3(A_216,k5_waybel_0(A_216,B_217),B_217)
      | ~ m1_subset_1(B_217,u1_struct_0(A_216))
      | ~ l1_orders_2(A_216) ) ),
    inference(resolution,[status(thm)],[c_355,c_10])).

tff(c_30,plain,(
    ! [A_20,B_32,C_38] :
      ( m1_subset_1('#skF_2'(A_20,B_32,C_38),u1_struct_0(A_20))
      | k1_yellow_0(A_20,C_38) = B_32
      | ~ r2_lattice3(A_20,C_38,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_20,C_38,B_32] :
      ( r2_lattice3(A_20,C_38,'#skF_2'(A_20,B_32,C_38))
      | k1_yellow_0(A_20,C_38) = B_32
      | ~ r2_lattice3(A_20,C_38,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_130,plain,(
    ! [C_101,A_102,B_103] :
      ( r2_hidden(C_101,k5_waybel_0(A_102,B_103))
      | ~ r1_orders_2(A_102,C_101,B_103)
      | ~ m1_subset_1(C_101,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8,plain,(
    ! [A_8,D_19,C_16,B_15] :
      ( r1_orders_2(A_8,D_19,C_16)
      | ~ r2_hidden(D_19,B_15)
      | ~ m1_subset_1(D_19,u1_struct_0(A_8))
      | ~ r2_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_264,plain,(
    ! [C_187,A_185,C_188,B_186,A_189] :
      ( r1_orders_2(A_185,C_187,C_188)
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ r2_lattice3(A_185,k5_waybel_0(A_189,B_186),C_188)
      | ~ m1_subset_1(C_188,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ r1_orders_2(A_189,C_187,B_186)
      | ~ m1_subset_1(C_187,u1_struct_0(A_189))
      | ~ m1_subset_1(B_186,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_274,plain,(
    ! [C_188,A_189,B_186] :
      ( r1_orders_2('#skF_4','#skF_5',C_188)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_189,B_186),C_188)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r1_orders_2(A_189,'#skF_5',B_186)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_189))
      | ~ m1_subset_1(B_186,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_64,c_264])).

tff(c_282,plain,(
    ! [C_190,A_191,B_192] :
      ( r1_orders_2('#skF_4','#skF_5',C_190)
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_191,B_192),C_190)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_191,'#skF_5',B_192)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_191))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_274])).

tff(c_286,plain,(
    ! [B_32,A_191,B_192] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_32,k5_waybel_0(A_191,B_192)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_32,k5_waybel_0(A_191,B_192)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_191,'#skF_5',B_192)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_191))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_orders_2(A_191)
      | v2_struct_0(A_191)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_191,B_192)) = B_32
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_191,B_192),B_32)
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_282])).

tff(c_376,plain,(
    ! [B_225,A_226,B_227] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_225,k5_waybel_0(A_226,B_227)))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_225,k5_waybel_0(A_226,B_227)),u1_struct_0('#skF_4'))
      | ~ r1_orders_2(A_226,'#skF_5',B_227)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_226))
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l1_orders_2(A_226)
      | v2_struct_0(A_226)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_226,B_227)) = B_225
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_226,B_227),B_225)
      | ~ m1_subset_1(B_225,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_286])).

tff(c_380,plain,(
    ! [B_32,A_226,B_227] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_32,k5_waybel_0(A_226,B_227)))
      | ~ r1_orders_2(A_226,'#skF_5',B_227)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_226))
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l1_orders_2(A_226)
      | v2_struct_0(A_226)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_226,B_227)) = B_32
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_226,B_227),B_32)
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_376])).

tff(c_476,plain,(
    ! [B_245,A_246,B_247] :
      ( r1_orders_2('#skF_4','#skF_5','#skF_2'('#skF_4',B_245,k5_waybel_0(A_246,B_247)))
      | ~ r1_orders_2(A_246,'#skF_5',B_247)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_246))
      | ~ m1_subset_1(B_247,u1_struct_0(A_246))
      | ~ l1_orders_2(A_246)
      | v2_struct_0(A_246)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_246,B_247)) = B_245
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_246,B_247),B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_380])).

tff(c_26,plain,(
    ! [A_20,B_32,C_38] :
      ( ~ r1_orders_2(A_20,B_32,'#skF_2'(A_20,B_32,C_38))
      | k1_yellow_0(A_20,C_38) = B_32
      | ~ r2_lattice3(A_20,C_38,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_480,plain,(
    ! [A_246,B_247] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_orders_2(A_246,'#skF_5',B_247)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_246))
      | ~ m1_subset_1(B_247,u1_struct_0(A_246))
      | ~ l1_orders_2(A_246)
      | v2_struct_0(A_246)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_246,B_247)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_246,B_247),'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_476,c_26])).

tff(c_491,plain,(
    ! [A_248,B_249] :
      ( ~ r1_orders_2(A_248,'#skF_5',B_249)
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_248))
      | ~ m1_subset_1(B_249,u1_struct_0(A_248))
      | ~ l1_orders_2(A_248)
      | v2_struct_0(A_248)
      | k1_yellow_0('#skF_4',k5_waybel_0(A_248,B_249)) = '#skF_5'
      | ~ r2_lattice3('#skF_4',k5_waybel_0(A_248,B_249),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72,c_66,c_480])).

tff(c_495,plain,
    ( ~ r1_orders_2('#skF_4','#skF_5','#skF_5')
    | k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_360,c_491])).

tff(c_498,plain,
    ( k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_102,c_495])).

tff(c_499,plain,(
    k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_498])).

tff(c_44,plain,(
    ! [A_55,C_64] :
      ( v4_waybel_7(k1_yellow_0(A_55,C_64),A_55)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ v1_waybel_7(C_64,A_55)
      | ~ v12_waybel_0(C_64,A_55)
      | ~ v1_waybel_0(C_64,A_55)
      | v1_xboole_0(C_64)
      | ~ m1_subset_1(k1_yellow_0(A_55,C_64),u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v2_lattice3(A_55)
      | ~ v1_lattice3(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_503,plain,
    ( v4_waybel_7(k1_yellow_0('#skF_4',k5_waybel_0('#skF_4','#skF_5')),'#skF_4')
    | ~ m1_subset_1(k5_waybel_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_44])).

tff(c_511,plain,
    ( v4_waybel_7('#skF_5','#skF_4')
    | ~ m1_subset_1(k5_waybel_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k5_waybel_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_499,c_503])).

tff(c_512,plain,
    ( ~ m1_subset_1(k5_waybel_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_60,c_511])).

tff(c_568,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_571,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_568])).

tff(c_574,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_64,c_571])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_574])).

tff(c_577,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k5_waybel_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_597,plain,(
    ~ m1_subset_1(k5_waybel_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_600,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_597])).

tff(c_603,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_600])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_603])).

tff(c_606,plain,
    ( ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_611,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_614,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_611])).

tff(c_617,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_64,c_614])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_617])).

tff(c_620,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_624,plain,
    ( ~ v5_waybel_6('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_620])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_62,c_624])).

tff(c_629,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_633,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_629,c_6])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.53  %$ r2_lattice3 > r1_orders_2 > v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.59/1.53  
% 3.59/1.53  %Foreground sorts:
% 3.59/1.53  
% 3.59/1.53  
% 3.59/1.53  %Background operators:
% 3.59/1.53  
% 3.59/1.53  
% 3.59/1.53  %Foreground operators:
% 3.59/1.53  tff(v1_waybel_7, type, v1_waybel_7: ($i * $i) > $o).
% 3.59/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.53  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.59/1.53  tff(v5_waybel_6, type, v5_waybel_6: ($i * $i) > $o).
% 3.59/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.59/1.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.59/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.53  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.59/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.59/1.53  tff(v12_waybel_0, type, v12_waybel_0: ($i * $i) > $o).
% 3.59/1.53  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.59/1.53  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.59/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.53  tff(v4_waybel_7, type, v4_waybel_7: ($i * $i) > $o).
% 3.59/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.59/1.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.59/1.53  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.59/1.53  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 3.59/1.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.59/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.59/1.53  tff(v1_waybel_0, type, v1_waybel_0: ($i * $i) > $o).
% 3.59/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.53  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.59/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.53  
% 3.68/1.56  tff(f_217, negated_conjecture, ~(![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v4_waybel_7(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 3.68/1.56  tff(f_197, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v1_waybel_7(k5_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 3.68/1.56  tff(f_43, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 3.68/1.56  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.68/1.56  tff(f_118, axiom, (![A, B]: ((((~v2_struct_0(A) & v4_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => v12_waybel_0(k5_waybel_0(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 3.68/1.56  tff(f_107, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k5_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 3.68/1.56  tff(f_132, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k5_waybel_0(A, B)) & v1_waybel_0(k5_waybel_0(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 3.68/1.56  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 3.68/1.56  tff(f_147, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k5_waybel_0(A, B)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_waybel_0)).
% 3.68/1.56  tff(f_98, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.68/1.56  tff(f_178, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v4_waybel_7(B, A) <=> (?[C]: (((((~v1_xboole_0(C) & v1_waybel_0(C, A)) & v12_waybel_0(C, A)) & v1_waybel_7(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) & (B = k1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 3.68/1.56  tff(c_66, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_70, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_76, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_74, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_72, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_68, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_62, plain, (v5_waybel_6('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_58, plain, (![A_65, B_67]: (v1_waybel_7(k5_waybel_0(A_65, B_67), A_65) | ~v5_waybel_6(B_67, A_65) | ~m1_subset_1(B_67, u1_struct_0(A_65)) | ~l1_orders_2(A_65) | ~v2_lattice3(A_65) | ~v1_lattice3(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.68/1.56  tff(c_87, plain, (![A_75, B_76]: (r1_orders_2(A_75, B_76, B_76) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.56  tff(c_89, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_87])).
% 3.68/1.56  tff(c_92, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_89])).
% 3.68/1.56  tff(c_94, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 3.68/1.56  tff(c_6, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.68/1.56  tff(c_97, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_94, c_6])).
% 3.68/1.56  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_97])).
% 3.68/1.56  tff(c_103, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 3.68/1.56  tff(c_34, plain, (![A_44, B_45]: (v12_waybel_0(k5_waybel_0(A_44, B_45), A_44) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | ~v4_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.68/1.56  tff(c_32, plain, (![A_42, B_43]: (m1_subset_1(k5_waybel_0(A_42, B_43), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_orders_2(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.68/1.56  tff(c_36, plain, (![A_46, B_47]: (v1_waybel_0(k5_waybel_0(A_46, B_47), A_46) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.68/1.56  tff(c_79, plain, (![A_73, B_74]: (~v1_xboole_0(k5_waybel_0(A_73, B_74)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.68/1.56  tff(c_82, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_79])).
% 3.68/1.56  tff(c_85, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_82])).
% 3.68/1.56  tff(c_86, plain, (~v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_85])).
% 3.68/1.56  tff(c_60, plain, (~v4_waybel_7('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 3.68/1.56  tff(c_102, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 3.68/1.56  tff(c_14, plain, (![A_8, B_15, C_16]: (m1_subset_1('#skF_1'(A_8, B_15, C_16), u1_struct_0(A_8)) | r2_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.56  tff(c_12, plain, (![A_8, B_15, C_16]: (r2_hidden('#skF_1'(A_8, B_15, C_16), B_15) | r2_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.56  tff(c_138, plain, (![A_104, C_105, B_106]: (r1_orders_2(A_104, C_105, B_106) | ~r2_hidden(C_105, k5_waybel_0(A_104, B_106)) | ~m1_subset_1(C_105, u1_struct_0(A_104)) | ~m1_subset_1(B_106, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.68/1.56  tff(c_331, plain, (![A_209, A_210, B_211, C_212]: (r1_orders_2(A_209, '#skF_1'(A_210, k5_waybel_0(A_209, B_211), C_212), B_211) | ~m1_subset_1('#skF_1'(A_210, k5_waybel_0(A_209, B_211), C_212), u1_struct_0(A_209)) | ~m1_subset_1(B_211, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | v2_struct_0(A_209) | r2_lattice3(A_210, k5_waybel_0(A_209, B_211), C_212) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~l1_orders_2(A_210))), inference(resolution, [status(thm)], [c_12, c_138])).
% 3.68/1.56  tff(c_355, plain, (![A_216, B_217, C_218]: (r1_orders_2(A_216, '#skF_1'(A_216, k5_waybel_0(A_216, B_217), C_218), B_217) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | v2_struct_0(A_216) | r2_lattice3(A_216, k5_waybel_0(A_216, B_217), C_218) | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~l1_orders_2(A_216))), inference(resolution, [status(thm)], [c_14, c_331])).
% 3.68/1.56  tff(c_10, plain, (![A_8, B_15, C_16]: (~r1_orders_2(A_8, '#skF_1'(A_8, B_15, C_16), C_16) | r2_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.56  tff(c_360, plain, (![A_216, B_217]: (v2_struct_0(A_216) | r2_lattice3(A_216, k5_waybel_0(A_216, B_217), B_217) | ~m1_subset_1(B_217, u1_struct_0(A_216)) | ~l1_orders_2(A_216))), inference(resolution, [status(thm)], [c_355, c_10])).
% 3.68/1.56  tff(c_30, plain, (![A_20, B_32, C_38]: (m1_subset_1('#skF_2'(A_20, B_32, C_38), u1_struct_0(A_20)) | k1_yellow_0(A_20, C_38)=B_32 | ~r2_lattice3(A_20, C_38, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.68/1.56  tff(c_28, plain, (![A_20, C_38, B_32]: (r2_lattice3(A_20, C_38, '#skF_2'(A_20, B_32, C_38)) | k1_yellow_0(A_20, C_38)=B_32 | ~r2_lattice3(A_20, C_38, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.68/1.56  tff(c_130, plain, (![C_101, A_102, B_103]: (r2_hidden(C_101, k5_waybel_0(A_102, B_103)) | ~r1_orders_2(A_102, C_101, B_103) | ~m1_subset_1(C_101, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.68/1.56  tff(c_8, plain, (![A_8, D_19, C_16, B_15]: (r1_orders_2(A_8, D_19, C_16) | ~r2_hidden(D_19, B_15) | ~m1_subset_1(D_19, u1_struct_0(A_8)) | ~r2_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.68/1.56  tff(c_264, plain, (![C_187, A_185, C_188, B_186, A_189]: (r1_orders_2(A_185, C_187, C_188) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~r2_lattice3(A_185, k5_waybel_0(A_189, B_186), C_188) | ~m1_subset_1(C_188, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~r1_orders_2(A_189, C_187, B_186) | ~m1_subset_1(C_187, u1_struct_0(A_189)) | ~m1_subset_1(B_186, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_130, c_8])).
% 3.68/1.56  tff(c_274, plain, (![C_188, A_189, B_186]: (r1_orders_2('#skF_4', '#skF_5', C_188) | ~r2_lattice3('#skF_4', k5_waybel_0(A_189, B_186), C_188) | ~m1_subset_1(C_188, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r1_orders_2(A_189, '#skF_5', B_186) | ~m1_subset_1('#skF_5', u1_struct_0(A_189)) | ~m1_subset_1(B_186, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_64, c_264])).
% 3.68/1.56  tff(c_282, plain, (![C_190, A_191, B_192]: (r1_orders_2('#skF_4', '#skF_5', C_190) | ~r2_lattice3('#skF_4', k5_waybel_0(A_191, B_192), C_190) | ~m1_subset_1(C_190, u1_struct_0('#skF_4')) | ~r1_orders_2(A_191, '#skF_5', B_192) | ~m1_subset_1('#skF_5', u1_struct_0(A_191)) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_orders_2(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_274])).
% 3.68/1.56  tff(c_286, plain, (![B_32, A_191, B_192]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_32, k5_waybel_0(A_191, B_192))) | ~m1_subset_1('#skF_2'('#skF_4', B_32, k5_waybel_0(A_191, B_192)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_191, '#skF_5', B_192) | ~m1_subset_1('#skF_5', u1_struct_0(A_191)) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_orders_2(A_191) | v2_struct_0(A_191) | k1_yellow_0('#skF_4', k5_waybel_0(A_191, B_192))=B_32 | ~r2_lattice3('#skF_4', k5_waybel_0(A_191, B_192), B_32) | ~m1_subset_1(B_32, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_282])).
% 3.68/1.56  tff(c_376, plain, (![B_225, A_226, B_227]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_225, k5_waybel_0(A_226, B_227))) | ~m1_subset_1('#skF_2'('#skF_4', B_225, k5_waybel_0(A_226, B_227)), u1_struct_0('#skF_4')) | ~r1_orders_2(A_226, '#skF_5', B_227) | ~m1_subset_1('#skF_5', u1_struct_0(A_226)) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l1_orders_2(A_226) | v2_struct_0(A_226) | k1_yellow_0('#skF_4', k5_waybel_0(A_226, B_227))=B_225 | ~r2_lattice3('#skF_4', k5_waybel_0(A_226, B_227), B_225) | ~m1_subset_1(B_225, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_286])).
% 3.68/1.56  tff(c_380, plain, (![B_32, A_226, B_227]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_32, k5_waybel_0(A_226, B_227))) | ~r1_orders_2(A_226, '#skF_5', B_227) | ~m1_subset_1('#skF_5', u1_struct_0(A_226)) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l1_orders_2(A_226) | v2_struct_0(A_226) | k1_yellow_0('#skF_4', k5_waybel_0(A_226, B_227))=B_32 | ~r2_lattice3('#skF_4', k5_waybel_0(A_226, B_227), B_32) | ~m1_subset_1(B_32, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_376])).
% 3.68/1.56  tff(c_476, plain, (![B_245, A_246, B_247]: (r1_orders_2('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_245, k5_waybel_0(A_246, B_247))) | ~r1_orders_2(A_246, '#skF_5', B_247) | ~m1_subset_1('#skF_5', u1_struct_0(A_246)) | ~m1_subset_1(B_247, u1_struct_0(A_246)) | ~l1_orders_2(A_246) | v2_struct_0(A_246) | k1_yellow_0('#skF_4', k5_waybel_0(A_246, B_247))=B_245 | ~r2_lattice3('#skF_4', k5_waybel_0(A_246, B_247), B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_380])).
% 3.68/1.56  tff(c_26, plain, (![A_20, B_32, C_38]: (~r1_orders_2(A_20, B_32, '#skF_2'(A_20, B_32, C_38)) | k1_yellow_0(A_20, C_38)=B_32 | ~r2_lattice3(A_20, C_38, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.68/1.56  tff(c_480, plain, (![A_246, B_247]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r1_orders_2(A_246, '#skF_5', B_247) | ~m1_subset_1('#skF_5', u1_struct_0(A_246)) | ~m1_subset_1(B_247, u1_struct_0(A_246)) | ~l1_orders_2(A_246) | v2_struct_0(A_246) | k1_yellow_0('#skF_4', k5_waybel_0(A_246, B_247))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_246, B_247), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_476, c_26])).
% 3.68/1.56  tff(c_491, plain, (![A_248, B_249]: (~r1_orders_2(A_248, '#skF_5', B_249) | ~m1_subset_1('#skF_5', u1_struct_0(A_248)) | ~m1_subset_1(B_249, u1_struct_0(A_248)) | ~l1_orders_2(A_248) | v2_struct_0(A_248) | k1_yellow_0('#skF_4', k5_waybel_0(A_248, B_249))='#skF_5' | ~r2_lattice3('#skF_4', k5_waybel_0(A_248, B_249), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72, c_66, c_480])).
% 3.68/1.56  tff(c_495, plain, (~r1_orders_2('#skF_4', '#skF_5', '#skF_5') | k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_360, c_491])).
% 3.68/1.56  tff(c_498, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_102, c_495])).
% 3.68/1.56  tff(c_499, plain, (k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_103, c_498])).
% 3.68/1.56  tff(c_44, plain, (![A_55, C_64]: (v4_waybel_7(k1_yellow_0(A_55, C_64), A_55) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_55))) | ~v1_waybel_7(C_64, A_55) | ~v12_waybel_0(C_64, A_55) | ~v1_waybel_0(C_64, A_55) | v1_xboole_0(C_64) | ~m1_subset_1(k1_yellow_0(A_55, C_64), u1_struct_0(A_55)) | ~l1_orders_2(A_55) | ~v2_lattice3(A_55) | ~v1_lattice3(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.68/1.56  tff(c_503, plain, (v4_waybel_7(k1_yellow_0('#skF_4', k5_waybel_0('#skF_4', '#skF_5')), '#skF_4') | ~m1_subset_1(k5_waybel_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_499, c_44])).
% 3.68/1.56  tff(c_511, plain, (v4_waybel_7('#skF_5', '#skF_4') | ~m1_subset_1(k5_waybel_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k5_waybel_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_499, c_503])).
% 3.68/1.56  tff(c_512, plain, (~m1_subset_1(k5_waybel_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_60, c_511])).
% 3.68/1.56  tff(c_568, plain, (~v1_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_512])).
% 3.68/1.56  tff(c_571, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_568])).
% 3.68/1.56  tff(c_574, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_64, c_571])).
% 3.68/1.56  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_574])).
% 3.68/1.56  tff(c_577, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1(k5_waybel_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_512])).
% 3.68/1.56  tff(c_597, plain, (~m1_subset_1(k5_waybel_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_577])).
% 3.68/1.56  tff(c_600, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_597])).
% 3.68/1.56  tff(c_603, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_600])).
% 3.68/1.56  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_603])).
% 3.68/1.56  tff(c_606, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4') | ~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_577])).
% 3.68/1.56  tff(c_611, plain, (~v12_waybel_0(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_606])).
% 3.68/1.56  tff(c_614, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_611])).
% 3.68/1.56  tff(c_617, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_64, c_614])).
% 3.68/1.56  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_617])).
% 3.68/1.56  tff(c_620, plain, (~v1_waybel_7(k5_waybel_0('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_606])).
% 3.68/1.56  tff(c_624, plain, (~v5_waybel_6('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_58, c_620])).
% 3.68/1.56  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_62, c_624])).
% 3.68/1.56  tff(c_629, plain, (v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_85])).
% 3.68/1.56  tff(c_633, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_629, c_6])).
% 3.68/1.56  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_633])).
% 3.68/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.56  
% 3.68/1.56  Inference rules
% 3.68/1.56  ----------------------
% 3.68/1.56  #Ref     : 0
% 3.68/1.56  #Sup     : 105
% 3.68/1.56  #Fact    : 0
% 3.68/1.56  #Define  : 0
% 3.68/1.56  #Split   : 5
% 3.68/1.56  #Chain   : 0
% 3.68/1.56  #Close   : 0
% 3.68/1.56  
% 3.68/1.56  Ordering : KBO
% 3.68/1.56  
% 3.68/1.56  Simplification rules
% 3.68/1.56  ----------------------
% 3.68/1.56  #Subsume      : 8
% 3.68/1.56  #Demod        : 112
% 3.68/1.56  #Tautology    : 23
% 3.68/1.56  #SimpNegUnit  : 12
% 3.68/1.56  #BackRed      : 0
% 3.68/1.56  
% 3.68/1.56  #Partial instantiations: 0
% 3.68/1.56  #Strategies tried      : 1
% 3.68/1.56  
% 3.68/1.56  Timing (in seconds)
% 3.68/1.56  ----------------------
% 3.68/1.56  Preprocessing        : 0.35
% 3.68/1.56  Parsing              : 0.19
% 3.68/1.56  CNF conversion       : 0.03
% 3.68/1.56  Main loop            : 0.44
% 3.68/1.56  Inferencing          : 0.18
% 3.68/1.56  Reduction            : 0.12
% 3.68/1.56  Demodulation         : 0.08
% 3.68/1.56  BG Simplification    : 0.03
% 3.68/1.56  Subsumption          : 0.09
% 3.68/1.56  Abstraction          : 0.02
% 3.68/1.56  MUC search           : 0.00
% 3.68/1.56  Cooper               : 0.00
% 3.68/1.56  Total                : 0.83
% 3.68/1.56  Index Insertion      : 0.00
% 3.68/1.56  Index Deletion       : 0.00
% 3.68/1.56  Index Matching       : 0.00
% 3.68/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
