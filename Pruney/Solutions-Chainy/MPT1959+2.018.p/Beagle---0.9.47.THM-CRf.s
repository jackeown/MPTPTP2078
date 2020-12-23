%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:00 EST 2020

% Result     : Theorem 13.58s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :  176 (1576 expanded)
%              Number of leaves         :   48 ( 556 expanded)
%              Depth                    :   28
%              Number of atoms          :  429 (5269 expanded)
%              Number of equality atoms :   51 ( 496 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

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

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_150,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_179,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_85,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_107,axiom,(
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

tff(f_143,axiom,(
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

tff(c_20,plain,(
    ! [A_16] : ~ v1_subset_1('#skF_3'(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1('#skF_3'(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    ! [B_99,A_100] :
      ( v1_subset_1(B_99,A_100)
      | B_99 = A_100
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_206,plain,(
    ! [A_16] :
      ( v1_subset_1('#skF_3'(A_16),A_16)
      | '#skF_3'(A_16) = A_16 ) ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_212,plain,(
    ! [A_16] : '#skF_3'(A_16) = A_16 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_206])).

tff(c_216,plain,(
    ! [A_16] : ~ v1_subset_1(A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_20])).

tff(c_215,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_22])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_96,plain,
    ( v1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_115,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_123,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(A_88,B_89)
      | v1_xboole_0(B_89)
      | ~ m1_subset_1(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,
    ( v1_xboole_0('#skF_9')
    | ~ m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_123,c_115])).

tff(c_132,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_126])).

tff(c_90,plain,
    ( r2_hidden(k3_yellow_0('#skF_8'),'#skF_9')
    | ~ v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_116,plain,(
    ~ v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_134,plain,(
    ! [B_90,A_91] :
      ( v1_subset_1(B_90,A_91)
      | B_90 = A_91
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_140,plain,
    ( v1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_70,c_134])).

tff(c_146,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_140])).

tff(c_78,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_106,plain,(
    ! [A_85] :
      ( k1_yellow_0(A_85,k1_xboole_0) = k3_yellow_0(A_85)
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_110,plain,(
    k1_yellow_0('#skF_8',k1_xboole_0) = k3_yellow_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_106])).

tff(c_117,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k1_yellow_0(A_86,B_87),u1_struct_0(A_86))
      | ~ l1_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_120,plain,
    ( m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_117])).

tff(c_122,plain,(
    m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_120])).

tff(c_159,plain,(
    m1_subset_1(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_122])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_159])).

tff(c_181,plain,(
    r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_181])).

tff(c_185,plain,(
    r2_hidden(k3_yellow_0('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_235,plain,(
    ! [C_104,A_105,B_106] :
      ( r2_hidden(C_104,A_105)
      | ~ r2_hidden(C_104,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    ! [A_107] :
      ( r2_hidden(k3_yellow_0('#skF_8'),A_107)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_185,c_235])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [A_108] :
      ( ~ v1_xboole_0(A_108)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_245,c_2])).

tff(c_262,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_70,c_253])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_975,plain,(
    ! [A_199,B_200,C_201] :
      ( m1_subset_1('#skF_2'(A_199,B_200,C_201),A_199)
      | C_201 = B_200
      | ~ m1_subset_1(C_201,k1_zfmisc_1(A_199))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_862,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_4'(A_183,B_184,C_185),B_184)
      | r2_lattice3(A_183,B_184,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_886,plain,(
    ! [B_184,A_183,C_185] :
      ( ~ v1_xboole_0(B_184)
      | r2_lattice3(A_183,B_184,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183) ) ),
    inference(resolution,[status(thm)],[c_862,c_2])).

tff(c_1029,plain,(
    ! [B_184,A_183,B_200,C_201] :
      ( ~ v1_xboole_0(B_184)
      | r2_lattice3(A_183,B_184,'#skF_2'(u1_struct_0(A_183),B_200,C_201))
      | ~ l1_orders_2(A_183)
      | C_201 = B_200
      | ~ m1_subset_1(C_201,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_183))) ) ),
    inference(resolution,[status(thm)],[c_975,c_886])).

tff(c_2283,plain,(
    ! [A_299,B_300,C_301] :
      ( r2_hidden('#skF_2'(A_299,B_300,C_301),B_300)
      | r2_hidden('#skF_2'(A_299,B_300,C_301),C_301)
      | C_301 = B_300
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_299))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(A_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_286,plain,(
    ! [A_112,C_113,B_114] :
      ( m1_subset_1(A_112,C_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(C_113))
      | ~ r2_hidden(A_112,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_291,plain,(
    ! [A_112,A_16] :
      ( m1_subset_1(A_112,A_16)
      | ~ r2_hidden(A_112,A_16) ) ),
    inference(resolution,[status(thm)],[c_215,c_286])).

tff(c_9085,plain,(
    ! [A_632,B_633,C_634] :
      ( m1_subset_1('#skF_2'(A_632,B_633,C_634),B_633)
      | r2_hidden('#skF_2'(A_632,B_633,C_634),C_634)
      | C_634 = B_633
      | ~ m1_subset_1(C_634,k1_zfmisc_1(A_632))
      | ~ m1_subset_1(B_633,k1_zfmisc_1(A_632)) ) ),
    inference(resolution,[status(thm)],[c_2283,c_291])).

tff(c_9431,plain,(
    ! [A_632,B_633,C_634] :
      ( m1_subset_1('#skF_2'(A_632,B_633,C_634),C_634)
      | m1_subset_1('#skF_2'(A_632,B_633,C_634),B_633)
      | C_634 = B_633
      | ~ m1_subset_1(C_634,k1_zfmisc_1(A_632))
      | ~ m1_subset_1(B_633,k1_zfmisc_1(A_632)) ) ),
    inference(resolution,[status(thm)],[c_9085,c_291])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,(
    ! [A_134,A_135,B_136] :
      ( r2_hidden(A_134,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_135))
      | v1_xboole_0(B_136)
      | ~ m1_subset_1(A_134,B_136) ) ),
    inference(resolution,[status(thm)],[c_24,c_235])).

tff(c_451,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,u1_struct_0('#skF_8'))
      | v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_134,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_70,c_438])).

tff(c_459,plain,(
    ! [A_137] :
      ( r2_hidden(A_137,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_451])).

tff(c_468,plain,(
    ! [A_137] :
      ( m1_subset_1(A_137,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_459,c_291])).

tff(c_913,plain,(
    ! [B_188,A_189,C_190] :
      ( ~ v1_xboole_0(B_188)
      | r2_lattice3(A_189,B_188,C_190)
      | ~ m1_subset_1(C_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189) ) ),
    inference(resolution,[status(thm)],[c_862,c_2])).

tff(c_929,plain,(
    ! [B_188,A_137] :
      ( ~ v1_xboole_0(B_188)
      | r2_lattice3('#skF_8',B_188,A_137)
      | ~ l1_orders_2('#skF_8')
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_468,c_913])).

tff(c_955,plain,(
    ! [B_188,A_137] :
      ( ~ v1_xboole_0(B_188)
      | r2_lattice3('#skF_8',B_188,A_137)
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_929])).

tff(c_72,plain,(
    v13_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_190,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(k1_yellow_0(A_95,B_96),u1_struct_0(A_95))
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_193,plain,
    ( m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_190])).

tff(c_195,plain,(
    m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_193])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_82,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_80,plain,(
    v1_yellow_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    ! [A_50] :
      ( r1_yellow_0(A_50,k1_xboole_0)
      | ~ l1_orders_2(A_50)
      | ~ v1_yellow_0(A_50)
      | ~ v5_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1199,plain,(
    ! [A_221,B_222] :
      ( r2_lattice3(A_221,B_222,k1_yellow_0(A_221,B_222))
      | ~ r1_yellow_0(A_221,B_222)
      | ~ m1_subset_1(k1_yellow_0(A_221,B_222),u1_struct_0(A_221))
      | ~ l1_orders_2(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1209,plain,
    ( r2_lattice3('#skF_8',k1_xboole_0,k1_yellow_0('#skF_8',k1_xboole_0))
    | ~ r1_yellow_0('#skF_8',k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8'))
    | ~ l1_orders_2('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1199])).

tff(c_1218,plain,
    ( r2_lattice3('#skF_8',k1_xboole_0,k3_yellow_0('#skF_8'))
    | ~ r1_yellow_0('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_195,c_110,c_1209])).

tff(c_1219,plain,(
    ~ r1_yellow_0('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1222,plain,
    ( ~ l1_orders_2('#skF_8')
    | ~ v1_yellow_0('#skF_8')
    | ~ v5_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_1219])).

tff(c_1225,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1222])).

tff(c_1227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1225])).

tff(c_1229,plain,(
    r1_yellow_0('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_3509,plain,(
    ! [A_377,B_378,D_379] :
      ( r1_orders_2(A_377,k1_yellow_0(A_377,B_378),D_379)
      | ~ r2_lattice3(A_377,B_378,D_379)
      | ~ m1_subset_1(D_379,u1_struct_0(A_377))
      | ~ r1_yellow_0(A_377,B_378)
      | ~ m1_subset_1(k1_yellow_0(A_377,B_378),u1_struct_0(A_377))
      | ~ l1_orders_2(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3519,plain,(
    ! [D_379] :
      ( r1_orders_2('#skF_8',k1_yellow_0('#skF_8',k1_xboole_0),D_379)
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_379)
      | ~ m1_subset_1(D_379,u1_struct_0('#skF_8'))
      | ~ r1_yellow_0('#skF_8',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_3509])).

tff(c_3528,plain,(
    ! [D_379] :
      ( r1_orders_2('#skF_8',k3_yellow_0('#skF_8'),D_379)
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_379)
      | ~ m1_subset_1(D_379,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_195,c_1229,c_110,c_3519])).

tff(c_3776,plain,(
    ! [D_405,B_406,A_407,C_408] :
      ( r2_hidden(D_405,B_406)
      | ~ r1_orders_2(A_407,C_408,D_405)
      | ~ r2_hidden(C_408,B_406)
      | ~ m1_subset_1(D_405,u1_struct_0(A_407))
      | ~ m1_subset_1(C_408,u1_struct_0(A_407))
      | ~ v13_waybel_0(B_406,A_407)
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ l1_orders_2(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3780,plain,(
    ! [D_379,B_406] :
      ( r2_hidden(D_379,B_406)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_406)
      | ~ m1_subset_1(k3_yellow_0('#skF_8'),u1_struct_0('#skF_8'))
      | ~ v13_waybel_0(B_406,'#skF_8')
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_379)
      | ~ m1_subset_1(D_379,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3528,c_3776])).

tff(c_13725,plain,(
    ! [D_743,B_744] :
      ( r2_hidden(D_743,B_744)
      | ~ r2_hidden(k3_yellow_0('#skF_8'),B_744)
      | ~ v13_waybel_0(B_744,'#skF_8')
      | ~ m1_subset_1(B_744,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_743)
      | ~ m1_subset_1(D_743,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_195,c_3780])).

tff(c_13808,plain,(
    ! [D_743] :
      ( r2_hidden(D_743,'#skF_9')
      | ~ r2_hidden(k3_yellow_0('#skF_8'),'#skF_9')
      | ~ v13_waybel_0('#skF_9','#skF_8')
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_743)
      | ~ m1_subset_1(D_743,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_13725])).

tff(c_13841,plain,(
    ! [D_745] :
      ( r2_hidden(D_745,'#skF_9')
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_745)
      | ~ m1_subset_1(D_745,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_185,c_13808])).

tff(c_14058,plain,(
    ! [A_746] :
      ( r2_hidden(A_746,'#skF_9')
      | ~ r2_lattice3('#skF_8',k1_xboole_0,A_746)
      | ~ m1_subset_1(A_746,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_468,c_13841])).

tff(c_14129,plain,(
    ! [A_137] :
      ( r2_hidden(A_137,'#skF_9')
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_955,c_14058])).

tff(c_14193,plain,(
    ! [A_137] :
      ( r2_hidden(A_137,'#skF_9')
      | ~ m1_subset_1(A_137,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14129])).

tff(c_2331,plain,(
    ! [A_299,B_300,C_301] :
      ( m1_subset_1('#skF_2'(A_299,B_300,C_301),B_300)
      | r2_hidden('#skF_2'(A_299,B_300,C_301),C_301)
      | C_301 = B_300
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_299))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(A_299)) ) ),
    inference(resolution,[status(thm)],[c_2283,c_291])).

tff(c_10,plain,(
    ! [A_9,B_10,C_14] :
      ( m1_subset_1('#skF_2'(A_9,B_10,C_14),A_9)
      | C_14 = B_10
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1829,plain,(
    ! [A_274,B_275,C_276] :
      ( ~ r2_hidden('#skF_2'(A_274,B_275,C_276),C_276)
      | ~ r2_hidden('#skF_2'(A_274,B_275,C_276),B_275)
      | C_276 = B_275
      | ~ m1_subset_1(C_276,k1_zfmisc_1(A_274))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(A_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5632,plain,(
    ! [A_487,B_488,B_489] :
      ( ~ r2_hidden('#skF_2'(A_487,B_488,B_489),B_488)
      | B_489 = B_488
      | ~ m1_subset_1(B_489,k1_zfmisc_1(A_487))
      | ~ m1_subset_1(B_488,k1_zfmisc_1(A_487))
      | v1_xboole_0(B_489)
      | ~ m1_subset_1('#skF_2'(A_487,B_488,B_489),B_489) ) ),
    inference(resolution,[status(thm)],[c_24,c_1829])).

tff(c_14919,plain,(
    ! [B_766,B_765,A_767] :
      ( B_766 = B_765
      | ~ m1_subset_1(B_765,k1_zfmisc_1(A_767))
      | ~ m1_subset_1(B_766,k1_zfmisc_1(A_767))
      | v1_xboole_0(B_765)
      | ~ m1_subset_1('#skF_2'(A_767,B_766,B_765),B_765)
      | v1_xboole_0(B_766)
      | ~ m1_subset_1('#skF_2'(A_767,B_766,B_765),B_766) ) ),
    inference(resolution,[status(thm)],[c_24,c_5632])).

tff(c_14944,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(A_9)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1('#skF_2'(A_9,B_10,A_9),B_10)
      | B_10 = A_9
      | ~ m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_10,c_14919])).

tff(c_18190,plain,(
    ! [A_847,B_848] :
      ( v1_xboole_0(A_847)
      | v1_xboole_0(B_848)
      | ~ m1_subset_1('#skF_2'(A_847,B_848,A_847),B_848)
      | B_848 = A_847
      | ~ m1_subset_1(B_848,k1_zfmisc_1(A_847)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_14944])).

tff(c_18210,plain,(
    ! [C_301,B_300] :
      ( v1_xboole_0(C_301)
      | v1_xboole_0(B_300)
      | r2_hidden('#skF_2'(C_301,B_300,C_301),C_301)
      | C_301 = B_300
      | ~ m1_subset_1(C_301,k1_zfmisc_1(C_301))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(C_301)) ) ),
    inference(resolution,[status(thm)],[c_2331,c_18190])).

tff(c_18520,plain,(
    ! [C_855,B_856] :
      ( v1_xboole_0(C_855)
      | v1_xboole_0(B_856)
      | r2_hidden('#skF_2'(C_855,B_856,C_855),C_855)
      | C_855 = B_856
      | ~ m1_subset_1(B_856,k1_zfmisc_1(C_855)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_18210])).

tff(c_12,plain,(
    ! [A_9,B_10,C_14] :
      ( ~ r2_hidden('#skF_2'(A_9,B_10,C_14),C_14)
      | ~ r2_hidden('#skF_2'(A_9,B_10,C_14),B_10)
      | C_14 = B_10
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18565,plain,(
    ! [C_855,B_856] :
      ( ~ r2_hidden('#skF_2'(C_855,B_856,C_855),B_856)
      | ~ m1_subset_1(C_855,k1_zfmisc_1(C_855))
      | v1_xboole_0(C_855)
      | v1_xboole_0(B_856)
      | C_855 = B_856
      | ~ m1_subset_1(B_856,k1_zfmisc_1(C_855)) ) ),
    inference(resolution,[status(thm)],[c_18520,c_12])).

tff(c_20298,plain,(
    ! [C_880,B_881] :
      ( ~ r2_hidden('#skF_2'(C_880,B_881,C_880),B_881)
      | v1_xboole_0(C_880)
      | v1_xboole_0(B_881)
      | C_880 = B_881
      | ~ m1_subset_1(B_881,k1_zfmisc_1(C_880)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_18565])).

tff(c_20318,plain,(
    ! [C_880] :
      ( v1_xboole_0(C_880)
      | v1_xboole_0('#skF_9')
      | C_880 = '#skF_9'
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(C_880))
      | ~ m1_subset_1('#skF_2'(C_880,'#skF_9',C_880),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14193,c_20298])).

tff(c_20653,plain,(
    ! [C_887] :
      ( v1_xboole_0(C_887)
      | C_887 = '#skF_9'
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(C_887))
      | ~ m1_subset_1('#skF_2'(C_887,'#skF_9',C_887),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_20318])).

tff(c_20663,plain,(
    ! [C_634] :
      ( v1_xboole_0(C_634)
      | m1_subset_1('#skF_2'(C_634,'#skF_9',C_634),C_634)
      | C_634 = '#skF_9'
      | ~ m1_subset_1(C_634,k1_zfmisc_1(C_634))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(C_634)) ) ),
    inference(resolution,[status(thm)],[c_9431,c_20653])).

tff(c_20730,plain,(
    ! [C_888] :
      ( v1_xboole_0(C_888)
      | m1_subset_1('#skF_2'(C_888,'#skF_9',C_888),C_888)
      | C_888 = '#skF_9'
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(C_888)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_20663])).

tff(c_13840,plain,(
    ! [D_743] :
      ( r2_hidden(D_743,'#skF_9')
      | ~ r2_lattice3('#skF_8',k1_xboole_0,D_743)
      | ~ m1_subset_1(D_743,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_185,c_13808])).

tff(c_20773,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')),'#skF_9')
    | ~ r2_lattice3('#skF_8',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')))
    | v1_xboole_0(u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_20730,c_13840])).

tff(c_21018,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')),'#skF_9')
    | ~ r2_lattice3('#skF_8',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')))
    | v1_xboole_0(u1_struct_0('#skF_8'))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20773])).

tff(c_21019,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')),'#skF_9')
    | ~ r2_lattice3('#skF_8',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')))
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_21018])).

tff(c_23008,plain,(
    ~ r2_lattice3('#skF_8',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_21019])).

tff(c_23011,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_orders_2('#skF_8')
    | u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_1029,c_23008])).

tff(c_23020,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_215,c_78,c_6,c_23011])).

tff(c_458,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(A_134,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_451])).

tff(c_5754,plain,(
    ! [B_494,A_495] :
      ( u1_struct_0('#skF_8') = B_494
      | ~ m1_subset_1(B_494,k1_zfmisc_1(A_495))
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(A_495))
      | v1_xboole_0(B_494)
      | ~ m1_subset_1('#skF_2'(A_495,u1_struct_0('#skF_8'),B_494),B_494)
      | ~ m1_subset_1('#skF_2'(A_495,u1_struct_0('#skF_8'),B_494),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_458,c_5632])).

tff(c_5763,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | ~ m1_subset_1('#skF_2'(A_9,u1_struct_0('#skF_8'),A_9),'#skF_9')
      | u1_struct_0('#skF_8') = A_9
      | ~ m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_10,c_5754])).

tff(c_5784,plain,(
    ! [A_496] :
      ( v1_xboole_0(A_496)
      | ~ m1_subset_1('#skF_2'(A_496,u1_struct_0('#skF_8'),A_496),'#skF_9')
      | u1_struct_0('#skF_8') = A_496
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(A_496)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_5763])).

tff(c_5792,plain,
    ( v1_xboole_0('#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_10,c_5784])).

tff(c_5799,plain,
    ( v1_xboole_0('#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_5792])).

tff(c_5800,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5799])).

tff(c_5801,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5800])).

tff(c_23104,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23020,c_5801])).

tff(c_23162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_23104])).

tff(c_23163,plain,
    ( u1_struct_0('#skF_8') = '#skF_9'
    | r2_hidden('#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_21019])).

tff(c_23216,plain,(
    r2_hidden('#skF_2'(u1_struct_0('#skF_8'),'#skF_9',u1_struct_0('#skF_8')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_23163])).

tff(c_18613,plain,(
    ! [C_855,B_856] :
      ( ~ r2_hidden('#skF_2'(C_855,B_856,C_855),B_856)
      | v1_xboole_0(C_855)
      | v1_xboole_0(B_856)
      | C_855 = B_856
      | ~ m1_subset_1(B_856,k1_zfmisc_1(C_855)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_18565])).

tff(c_23219,plain,
    ( v1_xboole_0(u1_struct_0('#skF_8'))
    | v1_xboole_0('#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_23216,c_18613])).

tff(c_23243,plain,
    ( v1_xboole_0(u1_struct_0('#skF_8'))
    | v1_xboole_0('#skF_9')
    | u1_struct_0('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_23219])).

tff(c_23244,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_262,c_23243])).

tff(c_23376,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23244,c_5801])).

tff(c_23434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_23376])).

tff(c_23435,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_23163])).

tff(c_23514,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23435,c_5801])).

tff(c_23572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_23514])).

tff(c_23573,plain,(
    u1_struct_0('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5800])).

tff(c_184,plain,(
    v1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_23618,plain,(
    v1_subset_1('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23573,c_184])).

tff(c_23623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_23618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n006.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.58/6.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/6.39  
% 13.60/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/6.39  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 13.60/6.39  
% 13.60/6.39  %Foreground sorts:
% 13.60/6.39  
% 13.60/6.39  
% 13.60/6.39  %Background operators:
% 13.60/6.39  
% 13.60/6.39  
% 13.60/6.39  %Foreground operators:
% 13.60/6.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.60/6.39  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 13.60/6.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.60/6.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 13.60/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.60/6.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.60/6.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 13.60/6.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.60/6.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 13.60/6.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.60/6.39  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 13.60/6.39  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 13.60/6.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.60/6.39  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 13.60/6.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.60/6.39  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 13.60/6.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.60/6.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 13.60/6.39  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 13.60/6.39  tff('#skF_9', type, '#skF_9': $i).
% 13.60/6.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 13.60/6.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.60/6.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 13.60/6.39  tff('#skF_8', type, '#skF_8': $i).
% 13.60/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.60/6.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.60/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.60/6.39  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 13.60/6.39  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.60/6.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.60/6.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.60/6.39  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 13.60/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.60/6.39  
% 13.75/6.42  tff(f_59, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 13.75/6.42  tff(f_150, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 13.75/6.42  tff(f_179, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 13.75/6.42  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 13.75/6.42  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 13.75/6.42  tff(f_111, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 13.75/6.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 13.75/6.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.75/6.42  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.75/6.42  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 13.75/6.42  tff(f_85, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 13.75/6.42  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 13.75/6.42  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 13.75/6.42  tff(f_107, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 13.75/6.42  tff(f_143, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 13.75/6.42  tff(c_20, plain, (![A_16]: (~v1_subset_1('#skF_3'(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.75/6.42  tff(c_22, plain, (![A_16]: (m1_subset_1('#skF_3'(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.75/6.42  tff(c_203, plain, (![B_99, A_100]: (v1_subset_1(B_99, A_100) | B_99=A_100 | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 13.75/6.42  tff(c_206, plain, (![A_16]: (v1_subset_1('#skF_3'(A_16), A_16) | '#skF_3'(A_16)=A_16)), inference(resolution, [status(thm)], [c_22, c_203])).
% 13.75/6.42  tff(c_212, plain, (![A_16]: ('#skF_3'(A_16)=A_16)), inference(negUnitSimplification, [status(thm)], [c_20, c_206])).
% 13.75/6.42  tff(c_216, plain, (![A_16]: (~v1_subset_1(A_16, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_20])).
% 13.75/6.42  tff(c_215, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_22])).
% 13.75/6.42  tff(c_76, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_96, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_115, plain, (~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_96])).
% 13.75/6.42  tff(c_123, plain, (![A_88, B_89]: (r2_hidden(A_88, B_89) | v1_xboole_0(B_89) | ~m1_subset_1(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.75/6.42  tff(c_126, plain, (v1_xboole_0('#skF_9') | ~m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_123, c_115])).
% 13.75/6.42  tff(c_132, plain, (~m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_76, c_126])).
% 13.75/6.42  tff(c_90, plain, (r2_hidden(k3_yellow_0('#skF_8'), '#skF_9') | ~v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_116, plain, (~v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_90])).
% 13.75/6.42  tff(c_134, plain, (![B_90, A_91]: (v1_subset_1(B_90, A_91) | B_90=A_91 | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 13.75/6.42  tff(c_140, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_70, c_134])).
% 13.75/6.42  tff(c_146, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_116, c_140])).
% 13.75/6.42  tff(c_78, plain, (l1_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_106, plain, (![A_85]: (k1_yellow_0(A_85, k1_xboole_0)=k3_yellow_0(A_85) | ~l1_orders_2(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.75/6.42  tff(c_110, plain, (k1_yellow_0('#skF_8', k1_xboole_0)=k3_yellow_0('#skF_8')), inference(resolution, [status(thm)], [c_78, c_106])).
% 13.75/6.42  tff(c_117, plain, (![A_86, B_87]: (m1_subset_1(k1_yellow_0(A_86, B_87), u1_struct_0(A_86)) | ~l1_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.75/6.42  tff(c_120, plain, (m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_110, c_117])).
% 13.75/6.42  tff(c_122, plain, (m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_120])).
% 13.75/6.42  tff(c_159, plain, (m1_subset_1(k3_yellow_0('#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_122])).
% 13.75/6.42  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_159])).
% 13.75/6.42  tff(c_181, plain, (r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_90])).
% 13.75/6.42  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_181])).
% 13.75/6.42  tff(c_185, plain, (r2_hidden(k3_yellow_0('#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_96])).
% 13.75/6.42  tff(c_235, plain, (![C_104, A_105, B_106]: (r2_hidden(C_104, A_105) | ~r2_hidden(C_104, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.75/6.42  tff(c_245, plain, (![A_107]: (r2_hidden(k3_yellow_0('#skF_8'), A_107) | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_107)))), inference(resolution, [status(thm)], [c_185, c_235])).
% 13.75/6.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/6.42  tff(c_253, plain, (![A_108]: (~v1_xboole_0(A_108) | ~m1_subset_1('#skF_9', k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_245, c_2])).
% 13.75/6.42  tff(c_262, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_70, c_253])).
% 13.75/6.42  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.75/6.42  tff(c_975, plain, (![A_199, B_200, C_201]: (m1_subset_1('#skF_2'(A_199, B_200, C_201), A_199) | C_201=B_200 | ~m1_subset_1(C_201, k1_zfmisc_1(A_199)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.42  tff(c_862, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_4'(A_183, B_184, C_185), B_184) | r2_lattice3(A_183, B_184, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_183)) | ~l1_orders_2(A_183))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.75/6.42  tff(c_886, plain, (![B_184, A_183, C_185]: (~v1_xboole_0(B_184) | r2_lattice3(A_183, B_184, C_185) | ~m1_subset_1(C_185, u1_struct_0(A_183)) | ~l1_orders_2(A_183))), inference(resolution, [status(thm)], [c_862, c_2])).
% 13.75/6.42  tff(c_1029, plain, (![B_184, A_183, B_200, C_201]: (~v1_xboole_0(B_184) | r2_lattice3(A_183, B_184, '#skF_2'(u1_struct_0(A_183), B_200, C_201)) | ~l1_orders_2(A_183) | C_201=B_200 | ~m1_subset_1(C_201, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_183))))), inference(resolution, [status(thm)], [c_975, c_886])).
% 13.75/6.42  tff(c_2283, plain, (![A_299, B_300, C_301]: (r2_hidden('#skF_2'(A_299, B_300, C_301), B_300) | r2_hidden('#skF_2'(A_299, B_300, C_301), C_301) | C_301=B_300 | ~m1_subset_1(C_301, k1_zfmisc_1(A_299)) | ~m1_subset_1(B_300, k1_zfmisc_1(A_299)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.42  tff(c_286, plain, (![A_112, C_113, B_114]: (m1_subset_1(A_112, C_113) | ~m1_subset_1(B_114, k1_zfmisc_1(C_113)) | ~r2_hidden(A_112, B_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.75/6.42  tff(c_291, plain, (![A_112, A_16]: (m1_subset_1(A_112, A_16) | ~r2_hidden(A_112, A_16))), inference(resolution, [status(thm)], [c_215, c_286])).
% 13.75/6.42  tff(c_9085, plain, (![A_632, B_633, C_634]: (m1_subset_1('#skF_2'(A_632, B_633, C_634), B_633) | r2_hidden('#skF_2'(A_632, B_633, C_634), C_634) | C_634=B_633 | ~m1_subset_1(C_634, k1_zfmisc_1(A_632)) | ~m1_subset_1(B_633, k1_zfmisc_1(A_632)))), inference(resolution, [status(thm)], [c_2283, c_291])).
% 13.75/6.42  tff(c_9431, plain, (![A_632, B_633, C_634]: (m1_subset_1('#skF_2'(A_632, B_633, C_634), C_634) | m1_subset_1('#skF_2'(A_632, B_633, C_634), B_633) | C_634=B_633 | ~m1_subset_1(C_634, k1_zfmisc_1(A_632)) | ~m1_subset_1(B_633, k1_zfmisc_1(A_632)))), inference(resolution, [status(thm)], [c_9085, c_291])).
% 13.75/6.42  tff(c_24, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.75/6.42  tff(c_438, plain, (![A_134, A_135, B_136]: (r2_hidden(A_134, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(A_135)) | v1_xboole_0(B_136) | ~m1_subset_1(A_134, B_136))), inference(resolution, [status(thm)], [c_24, c_235])).
% 13.75/6.42  tff(c_451, plain, (![A_134]: (r2_hidden(A_134, u1_struct_0('#skF_8')) | v1_xboole_0('#skF_9') | ~m1_subset_1(A_134, '#skF_9'))), inference(resolution, [status(thm)], [c_70, c_438])).
% 13.75/6.42  tff(c_459, plain, (![A_137]: (r2_hidden(A_137, u1_struct_0('#skF_8')) | ~m1_subset_1(A_137, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_76, c_451])).
% 13.75/6.42  tff(c_468, plain, (![A_137]: (m1_subset_1(A_137, u1_struct_0('#skF_8')) | ~m1_subset_1(A_137, '#skF_9'))), inference(resolution, [status(thm)], [c_459, c_291])).
% 13.75/6.42  tff(c_913, plain, (![B_188, A_189, C_190]: (~v1_xboole_0(B_188) | r2_lattice3(A_189, B_188, C_190) | ~m1_subset_1(C_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189))), inference(resolution, [status(thm)], [c_862, c_2])).
% 13.75/6.42  tff(c_929, plain, (![B_188, A_137]: (~v1_xboole_0(B_188) | r2_lattice3('#skF_8', B_188, A_137) | ~l1_orders_2('#skF_8') | ~m1_subset_1(A_137, '#skF_9'))), inference(resolution, [status(thm)], [c_468, c_913])).
% 13.75/6.42  tff(c_955, plain, (![B_188, A_137]: (~v1_xboole_0(B_188) | r2_lattice3('#skF_8', B_188, A_137) | ~m1_subset_1(A_137, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_929])).
% 13.75/6.42  tff(c_72, plain, (v13_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_190, plain, (![A_95, B_96]: (m1_subset_1(k1_yellow_0(A_95, B_96), u1_struct_0(A_95)) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.75/6.42  tff(c_193, plain, (m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_110, c_190])).
% 13.75/6.42  tff(c_195, plain, (m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_193])).
% 13.75/6.42  tff(c_88, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_82, plain, (v5_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_80, plain, (v1_yellow_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.75/6.42  tff(c_52, plain, (![A_50]: (r1_yellow_0(A_50, k1_xboole_0) | ~l1_orders_2(A_50) | ~v1_yellow_0(A_50) | ~v5_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/6.42  tff(c_1199, plain, (![A_221, B_222]: (r2_lattice3(A_221, B_222, k1_yellow_0(A_221, B_222)) | ~r1_yellow_0(A_221, B_222) | ~m1_subset_1(k1_yellow_0(A_221, B_222), u1_struct_0(A_221)) | ~l1_orders_2(A_221))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.75/6.42  tff(c_1209, plain, (r2_lattice3('#skF_8', k1_xboole_0, k1_yellow_0('#skF_8', k1_xboole_0)) | ~r1_yellow_0('#skF_8', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_110, c_1199])).
% 13.75/6.42  tff(c_1218, plain, (r2_lattice3('#skF_8', k1_xboole_0, k3_yellow_0('#skF_8')) | ~r1_yellow_0('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_195, c_110, c_1209])).
% 13.75/6.42  tff(c_1219, plain, (~r1_yellow_0('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1218])).
% 13.75/6.42  tff(c_1222, plain, (~l1_orders_2('#skF_8') | ~v1_yellow_0('#skF_8') | ~v5_orders_2('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_52, c_1219])).
% 13.75/6.42  tff(c_1225, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1222])).
% 13.75/6.42  tff(c_1227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1225])).
% 13.75/6.42  tff(c_1229, plain, (r1_yellow_0('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1218])).
% 13.75/6.42  tff(c_3509, plain, (![A_377, B_378, D_379]: (r1_orders_2(A_377, k1_yellow_0(A_377, B_378), D_379) | ~r2_lattice3(A_377, B_378, D_379) | ~m1_subset_1(D_379, u1_struct_0(A_377)) | ~r1_yellow_0(A_377, B_378) | ~m1_subset_1(k1_yellow_0(A_377, B_378), u1_struct_0(A_377)) | ~l1_orders_2(A_377))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.75/6.42  tff(c_3519, plain, (![D_379]: (r1_orders_2('#skF_8', k1_yellow_0('#skF_8', k1_xboole_0), D_379) | ~r2_lattice3('#skF_8', k1_xboole_0, D_379) | ~m1_subset_1(D_379, u1_struct_0('#skF_8')) | ~r1_yellow_0('#skF_8', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_3509])).
% 13.75/6.42  tff(c_3528, plain, (![D_379]: (r1_orders_2('#skF_8', k3_yellow_0('#skF_8'), D_379) | ~r2_lattice3('#skF_8', k1_xboole_0, D_379) | ~m1_subset_1(D_379, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_195, c_1229, c_110, c_3519])).
% 13.75/6.42  tff(c_3776, plain, (![D_405, B_406, A_407, C_408]: (r2_hidden(D_405, B_406) | ~r1_orders_2(A_407, C_408, D_405) | ~r2_hidden(C_408, B_406) | ~m1_subset_1(D_405, u1_struct_0(A_407)) | ~m1_subset_1(C_408, u1_struct_0(A_407)) | ~v13_waybel_0(B_406, A_407) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_407))) | ~l1_orders_2(A_407))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.75/6.42  tff(c_3780, plain, (![D_379, B_406]: (r2_hidden(D_379, B_406) | ~r2_hidden(k3_yellow_0('#skF_8'), B_406) | ~m1_subset_1(k3_yellow_0('#skF_8'), u1_struct_0('#skF_8')) | ~v13_waybel_0(B_406, '#skF_8') | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~l1_orders_2('#skF_8') | ~r2_lattice3('#skF_8', k1_xboole_0, D_379) | ~m1_subset_1(D_379, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_3528, c_3776])).
% 13.75/6.42  tff(c_13725, plain, (![D_743, B_744]: (r2_hidden(D_743, B_744) | ~r2_hidden(k3_yellow_0('#skF_8'), B_744) | ~v13_waybel_0(B_744, '#skF_8') | ~m1_subset_1(B_744, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~r2_lattice3('#skF_8', k1_xboole_0, D_743) | ~m1_subset_1(D_743, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_195, c_3780])).
% 13.75/6.42  tff(c_13808, plain, (![D_743]: (r2_hidden(D_743, '#skF_9') | ~r2_hidden(k3_yellow_0('#skF_8'), '#skF_9') | ~v13_waybel_0('#skF_9', '#skF_8') | ~r2_lattice3('#skF_8', k1_xboole_0, D_743) | ~m1_subset_1(D_743, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_13725])).
% 13.75/6.42  tff(c_13841, plain, (![D_745]: (r2_hidden(D_745, '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, D_745) | ~m1_subset_1(D_745, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_185, c_13808])).
% 13.75/6.42  tff(c_14058, plain, (![A_746]: (r2_hidden(A_746, '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, A_746) | ~m1_subset_1(A_746, '#skF_9'))), inference(resolution, [status(thm)], [c_468, c_13841])).
% 13.75/6.42  tff(c_14129, plain, (![A_137]: (r2_hidden(A_137, '#skF_9') | ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_137, '#skF_9'))), inference(resolution, [status(thm)], [c_955, c_14058])).
% 13.75/6.42  tff(c_14193, plain, (![A_137]: (r2_hidden(A_137, '#skF_9') | ~m1_subset_1(A_137, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14129])).
% 13.75/6.42  tff(c_2331, plain, (![A_299, B_300, C_301]: (m1_subset_1('#skF_2'(A_299, B_300, C_301), B_300) | r2_hidden('#skF_2'(A_299, B_300, C_301), C_301) | C_301=B_300 | ~m1_subset_1(C_301, k1_zfmisc_1(A_299)) | ~m1_subset_1(B_300, k1_zfmisc_1(A_299)))), inference(resolution, [status(thm)], [c_2283, c_291])).
% 13.75/6.42  tff(c_10, plain, (![A_9, B_10, C_14]: (m1_subset_1('#skF_2'(A_9, B_10, C_14), A_9) | C_14=B_10 | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.42  tff(c_1829, plain, (![A_274, B_275, C_276]: (~r2_hidden('#skF_2'(A_274, B_275, C_276), C_276) | ~r2_hidden('#skF_2'(A_274, B_275, C_276), B_275) | C_276=B_275 | ~m1_subset_1(C_276, k1_zfmisc_1(A_274)) | ~m1_subset_1(B_275, k1_zfmisc_1(A_274)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.42  tff(c_5632, plain, (![A_487, B_488, B_489]: (~r2_hidden('#skF_2'(A_487, B_488, B_489), B_488) | B_489=B_488 | ~m1_subset_1(B_489, k1_zfmisc_1(A_487)) | ~m1_subset_1(B_488, k1_zfmisc_1(A_487)) | v1_xboole_0(B_489) | ~m1_subset_1('#skF_2'(A_487, B_488, B_489), B_489))), inference(resolution, [status(thm)], [c_24, c_1829])).
% 13.75/6.42  tff(c_14919, plain, (![B_766, B_765, A_767]: (B_766=B_765 | ~m1_subset_1(B_765, k1_zfmisc_1(A_767)) | ~m1_subset_1(B_766, k1_zfmisc_1(A_767)) | v1_xboole_0(B_765) | ~m1_subset_1('#skF_2'(A_767, B_766, B_765), B_765) | v1_xboole_0(B_766) | ~m1_subset_1('#skF_2'(A_767, B_766, B_765), B_766))), inference(resolution, [status(thm)], [c_24, c_5632])).
% 13.75/6.42  tff(c_14944, plain, (![A_9, B_10]: (v1_xboole_0(A_9) | v1_xboole_0(B_10) | ~m1_subset_1('#skF_2'(A_9, B_10, A_9), B_10) | B_10=A_9 | ~m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_10, c_14919])).
% 13.75/6.42  tff(c_18190, plain, (![A_847, B_848]: (v1_xboole_0(A_847) | v1_xboole_0(B_848) | ~m1_subset_1('#skF_2'(A_847, B_848, A_847), B_848) | B_848=A_847 | ~m1_subset_1(B_848, k1_zfmisc_1(A_847)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_14944])).
% 13.75/6.42  tff(c_18210, plain, (![C_301, B_300]: (v1_xboole_0(C_301) | v1_xboole_0(B_300) | r2_hidden('#skF_2'(C_301, B_300, C_301), C_301) | C_301=B_300 | ~m1_subset_1(C_301, k1_zfmisc_1(C_301)) | ~m1_subset_1(B_300, k1_zfmisc_1(C_301)))), inference(resolution, [status(thm)], [c_2331, c_18190])).
% 13.75/6.42  tff(c_18520, plain, (![C_855, B_856]: (v1_xboole_0(C_855) | v1_xboole_0(B_856) | r2_hidden('#skF_2'(C_855, B_856, C_855), C_855) | C_855=B_856 | ~m1_subset_1(B_856, k1_zfmisc_1(C_855)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_18210])).
% 13.75/6.42  tff(c_12, plain, (![A_9, B_10, C_14]: (~r2_hidden('#skF_2'(A_9, B_10, C_14), C_14) | ~r2_hidden('#skF_2'(A_9, B_10, C_14), B_10) | C_14=B_10 | ~m1_subset_1(C_14, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.75/6.42  tff(c_18565, plain, (![C_855, B_856]: (~r2_hidden('#skF_2'(C_855, B_856, C_855), B_856) | ~m1_subset_1(C_855, k1_zfmisc_1(C_855)) | v1_xboole_0(C_855) | v1_xboole_0(B_856) | C_855=B_856 | ~m1_subset_1(B_856, k1_zfmisc_1(C_855)))), inference(resolution, [status(thm)], [c_18520, c_12])).
% 13.75/6.42  tff(c_20298, plain, (![C_880, B_881]: (~r2_hidden('#skF_2'(C_880, B_881, C_880), B_881) | v1_xboole_0(C_880) | v1_xboole_0(B_881) | C_880=B_881 | ~m1_subset_1(B_881, k1_zfmisc_1(C_880)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_18565])).
% 13.75/6.42  tff(c_20318, plain, (![C_880]: (v1_xboole_0(C_880) | v1_xboole_0('#skF_9') | C_880='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(C_880)) | ~m1_subset_1('#skF_2'(C_880, '#skF_9', C_880), '#skF_9'))), inference(resolution, [status(thm)], [c_14193, c_20298])).
% 13.75/6.42  tff(c_20653, plain, (![C_887]: (v1_xboole_0(C_887) | C_887='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(C_887)) | ~m1_subset_1('#skF_2'(C_887, '#skF_9', C_887), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_76, c_20318])).
% 13.75/6.42  tff(c_20663, plain, (![C_634]: (v1_xboole_0(C_634) | m1_subset_1('#skF_2'(C_634, '#skF_9', C_634), C_634) | C_634='#skF_9' | ~m1_subset_1(C_634, k1_zfmisc_1(C_634)) | ~m1_subset_1('#skF_9', k1_zfmisc_1(C_634)))), inference(resolution, [status(thm)], [c_9431, c_20653])).
% 13.75/6.42  tff(c_20730, plain, (![C_888]: (v1_xboole_0(C_888) | m1_subset_1('#skF_2'(C_888, '#skF_9', C_888), C_888) | C_888='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(C_888)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_20663])).
% 13.75/6.42  tff(c_13840, plain, (![D_743]: (r2_hidden(D_743, '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, D_743) | ~m1_subset_1(D_743, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_185, c_13808])).
% 13.75/6.42  tff(c_20773, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')), '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8'))) | v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_20730, c_13840])).
% 13.75/6.42  tff(c_21018, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')), '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8'))) | v1_xboole_0(u1_struct_0('#skF_8')) | u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20773])).
% 13.75/6.42  tff(c_21019, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')), '#skF_9') | ~r2_lattice3('#skF_8', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8'))) | u1_struct_0('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_262, c_21018])).
% 13.75/6.42  tff(c_23008, plain, (~r2_lattice3('#skF_8', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')))), inference(splitLeft, [status(thm)], [c_21019])).
% 13.75/6.42  tff(c_23011, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_orders_2('#skF_8') | u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_1029, c_23008])).
% 13.75/6.42  tff(c_23020, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_215, c_78, c_6, c_23011])).
% 13.75/6.42  tff(c_458, plain, (![A_134]: (r2_hidden(A_134, u1_struct_0('#skF_8')) | ~m1_subset_1(A_134, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_76, c_451])).
% 13.75/6.42  tff(c_5754, plain, (![B_494, A_495]: (u1_struct_0('#skF_8')=B_494 | ~m1_subset_1(B_494, k1_zfmisc_1(A_495)) | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(A_495)) | v1_xboole_0(B_494) | ~m1_subset_1('#skF_2'(A_495, u1_struct_0('#skF_8'), B_494), B_494) | ~m1_subset_1('#skF_2'(A_495, u1_struct_0('#skF_8'), B_494), '#skF_9'))), inference(resolution, [status(thm)], [c_458, c_5632])).
% 13.75/6.42  tff(c_5763, plain, (![A_9]: (v1_xboole_0(A_9) | ~m1_subset_1('#skF_2'(A_9, u1_struct_0('#skF_8'), A_9), '#skF_9') | u1_struct_0('#skF_8')=A_9 | ~m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_10, c_5754])).
% 13.75/6.42  tff(c_5784, plain, (![A_496]: (v1_xboole_0(A_496) | ~m1_subset_1('#skF_2'(A_496, u1_struct_0('#skF_8'), A_496), '#skF_9') | u1_struct_0('#skF_8')=A_496 | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(A_496)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_5763])).
% 13.75/6.42  tff(c_5792, plain, (v1_xboole_0('#skF_9') | u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9')) | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_10, c_5784])).
% 13.75/6.42  tff(c_5799, plain, (v1_xboole_0('#skF_9') | u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_5792])).
% 13.75/6.42  tff(c_5800, plain, (u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_76, c_5799])).
% 13.75/6.42  tff(c_5801, plain, (~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_5800])).
% 13.75/6.42  tff(c_23104, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_23020, c_5801])).
% 13.75/6.42  tff(c_23162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_23104])).
% 13.75/6.42  tff(c_23163, plain, (u1_struct_0('#skF_8')='#skF_9' | r2_hidden('#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(splitRight, [status(thm)], [c_21019])).
% 13.75/6.42  tff(c_23216, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_8'), '#skF_9', u1_struct_0('#skF_8')), '#skF_9')), inference(splitLeft, [status(thm)], [c_23163])).
% 13.75/6.42  tff(c_18613, plain, (![C_855, B_856]: (~r2_hidden('#skF_2'(C_855, B_856, C_855), B_856) | v1_xboole_0(C_855) | v1_xboole_0(B_856) | C_855=B_856 | ~m1_subset_1(B_856, k1_zfmisc_1(C_855)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_18565])).
% 13.75/6.42  tff(c_23219, plain, (v1_xboole_0(u1_struct_0('#skF_8')) | v1_xboole_0('#skF_9') | u1_struct_0('#skF_8')='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_23216, c_18613])).
% 13.75/6.42  tff(c_23243, plain, (v1_xboole_0(u1_struct_0('#skF_8')) | v1_xboole_0('#skF_9') | u1_struct_0('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_23219])).
% 13.75/6.42  tff(c_23244, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_76, c_262, c_23243])).
% 13.75/6.42  tff(c_23376, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_23244, c_5801])).
% 13.75/6.42  tff(c_23434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_23376])).
% 13.75/6.42  tff(c_23435, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_23163])).
% 13.75/6.42  tff(c_23514, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_23435, c_5801])).
% 13.75/6.42  tff(c_23572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_23514])).
% 13.75/6.42  tff(c_23573, plain, (u1_struct_0('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_5800])).
% 13.75/6.42  tff(c_184, plain, (v1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_96])).
% 13.75/6.42  tff(c_23618, plain, (v1_subset_1('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_23573, c_184])).
% 13.75/6.42  tff(c_23623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_23618])).
% 13.75/6.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/6.42  
% 13.75/6.42  Inference rules
% 13.75/6.42  ----------------------
% 13.75/6.42  #Ref     : 0
% 13.75/6.42  #Sup     : 5024
% 13.75/6.42  #Fact    : 16
% 13.75/6.42  #Define  : 0
% 13.75/6.42  #Split   : 25
% 13.75/6.42  #Chain   : 0
% 13.75/6.42  #Close   : 0
% 13.75/6.42  
% 13.75/6.42  Ordering : KBO
% 13.75/6.42  
% 13.75/6.42  Simplification rules
% 13.75/6.42  ----------------------
% 13.75/6.42  #Subsume      : 1104
% 13.75/6.42  #Demod        : 1714
% 13.75/6.42  #Tautology    : 390
% 13.75/6.42  #SimpNegUnit  : 121
% 13.75/6.42  #BackRed      : 423
% 13.75/6.42  
% 13.75/6.42  #Partial instantiations: 0
% 13.75/6.42  #Strategies tried      : 1
% 13.75/6.42  
% 13.75/6.42  Timing (in seconds)
% 13.75/6.42  ----------------------
% 13.75/6.42  Preprocessing        : 0.37
% 13.75/6.42  Parsing              : 0.19
% 13.75/6.42  CNF conversion       : 0.03
% 13.75/6.42  Main loop            : 5.26
% 13.75/6.42  Inferencing          : 0.97
% 13.75/6.42  Reduction            : 1.19
% 13.75/6.42  Demodulation         : 0.82
% 13.75/6.42  BG Simplification    : 0.13
% 13.75/6.42  Subsumption          : 2.61
% 13.75/6.42  Abstraction          : 0.18
% 13.75/6.42  MUC search           : 0.00
% 13.75/6.42  Cooper               : 0.00
% 13.75/6.42  Total                : 5.68
% 13.75/6.42  Index Insertion      : 0.00
% 13.75/6.42  Index Deletion       : 0.00
% 13.75/6.42  Index Matching       : 0.00
% 13.75/6.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
