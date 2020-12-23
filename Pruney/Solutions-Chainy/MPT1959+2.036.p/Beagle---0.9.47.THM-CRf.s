%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:02 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 389 expanded)
%              Number of leaves         :   44 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 (1488 expanded)
%              Number of equality atoms :   35 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_142,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [A_4] : ~ v1_subset_1('#skF_2'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1('#skF_2'(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_158,plain,(
    ! [B_84,A_85] :
      ( v1_subset_1(B_84,A_85)
      | B_84 = A_85
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_161,plain,(
    ! [A_4] :
      ( v1_subset_1('#skF_2'(A_4),A_4)
      | '#skF_2'(A_4) = A_4 ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_167,plain,(
    ! [A_4] : '#skF_2'(A_4) = A_4 ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_161])).

tff(c_171,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_6])).

tff(c_170,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_261,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1('#skF_1'(A_107,B_108),A_107)
      | B_108 = A_107
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [A_37,B_39] :
      ( r2_lattice3(A_37,k1_xboole_0,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_277,plain,(
    ! [A_37,B_108] :
      ( r2_lattice3(A_37,k1_xboole_0,'#skF_1'(u1_struct_0(A_37),B_108))
      | ~ l1_orders_2(A_37)
      | u1_struct_0(A_37) = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_37))) ) ),
    inference(resolution,[status(thm)],[c_261,c_40])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_105,plain,(
    ! [A_74,B_75] :
      ( r2_hidden(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_84,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_103,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_105,c_103])).

tff(c_111,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_108])).

tff(c_78,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_104,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_78])).

tff(c_112,plain,(
    ! [B_76,A_77] :
      ( v1_subset_1(B_76,A_77)
      | B_76 = A_77
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_118,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_124,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_118])).

tff(c_88,plain,(
    ! [A_71] :
      ( k1_yellow_0(A_71,k1_xboole_0) = k3_yellow_0(A_71)
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_88])).

tff(c_97,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k1_yellow_0(A_72,B_73),u1_struct_0(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_97])).

tff(c_102,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_100])).

tff(c_149,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_102])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_149])).

tff(c_154,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_70,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_68,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_36,plain,(
    ! [A_36] :
      ( r1_yellow_0(A_36,k1_xboole_0)
      | ~ l1_orders_2(A_36)
      | ~ v1_yellow_0(A_36)
      | ~ v5_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1139,plain,(
    ! [A_283,C_284,D_285] :
      ( r1_orders_2(A_283,k1_yellow_0(A_283,C_284),D_285)
      | ~ r2_lattice3(A_283,C_284,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0(A_283))
      | ~ r1_yellow_0(A_283,C_284)
      | ~ m1_subset_1(k1_yellow_0(A_283,C_284),u1_struct_0(A_283))
      | ~ l1_orders_2(A_283)
      | ~ v5_orders_2(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1146,plain,(
    ! [D_285] :
      ( r1_orders_2('#skF_6',k1_yellow_0('#skF_6',k1_xboole_0),D_285)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1139])).

tff(c_1152,plain,(
    ! [D_285] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_285)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_102,c_92,c_1146])).

tff(c_1153,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1152])).

tff(c_1156,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_1153])).

tff(c_1159,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1156])).

tff(c_1161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1159])).

tff(c_1162,plain,(
    ! [D_285] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_285)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_1195,plain,(
    ! [D_290,B_291,A_292,C_293] :
      ( r2_hidden(D_290,B_291)
      | ~ r1_orders_2(A_292,C_293,D_290)
      | ~ r2_hidden(C_293,B_291)
      | ~ m1_subset_1(D_290,u1_struct_0(A_292))
      | ~ m1_subset_1(C_293,u1_struct_0(A_292))
      | ~ v13_waybel_0(B_291,A_292)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_orders_2(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1199,plain,(
    ! [D_285,B_291] :
      ( r2_hidden(D_285,B_291)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_291)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_291,'#skF_6')
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_285)
      | ~ m1_subset_1(D_285,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1162,c_1195])).

tff(c_1243,plain,(
    ! [D_305,B_306] :
      ( r2_hidden(D_305,B_306)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_306)
      | ~ v13_waybel_0(B_306,'#skF_6')
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_305)
      | ~ m1_subset_1(D_305,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_102,c_1199])).

tff(c_1251,plain,(
    ! [D_305] :
      ( r2_hidden(D_305,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_305)
      | ~ m1_subset_1(D_305,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_58,c_1243])).

tff(c_1257,plain,(
    ! [D_307] :
      ( r2_hidden(D_307,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_307)
      | ~ m1_subset_1(D_307,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154,c_1251])).

tff(c_1391,plain,(
    ! [B_314] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_314),'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),B_314))
      | u1_struct_0('#skF_6') = B_314
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1257])).

tff(c_1395,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_108),'#skF_7')
      | ~ l1_orders_2('#skF_6')
      | u1_struct_0('#skF_6') = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_277,c_1391])).

tff(c_1409,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_315),'#skF_7')
      | u1_struct_0('#skF_6') = B_315
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1395])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | B_2 = A_1
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1417,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1409,c_2])).

tff(c_1427,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1417])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_511,plain,(
    ! [A_185,C_186,D_187] :
      ( r1_orders_2(A_185,k1_yellow_0(A_185,C_186),D_187)
      | ~ r2_lattice3(A_185,C_186,D_187)
      | ~ m1_subset_1(D_187,u1_struct_0(A_185))
      | ~ r1_yellow_0(A_185,C_186)
      | ~ m1_subset_1(k1_yellow_0(A_185,C_186),u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ v5_orders_2(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_518,plain,(
    ! [D_187] :
      ( r1_orders_2('#skF_6',k1_yellow_0('#skF_6',k1_xboole_0),D_187)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_187)
      | ~ m1_subset_1(D_187,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_511])).

tff(c_524,plain,(
    ! [D_187] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_187)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_187)
      | ~ m1_subset_1(D_187,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_102,c_92,c_518])).

tff(c_525,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_528,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_525])).

tff(c_531,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_528])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_531])).

tff(c_534,plain,(
    ! [D_187] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_187)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_187)
      | ~ m1_subset_1(D_187,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_567,plain,(
    ! [D_192,B_193,A_194,C_195] :
      ( r2_hidden(D_192,B_193)
      | ~ r1_orders_2(A_194,C_195,D_192)
      | ~ r2_hidden(C_195,B_193)
      | ~ m1_subset_1(D_192,u1_struct_0(A_194))
      | ~ m1_subset_1(C_195,u1_struct_0(A_194))
      | ~ v13_waybel_0(B_193,A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_orders_2(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_571,plain,(
    ! [D_187,B_193] :
      ( r2_hidden(D_187,B_193)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_193)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_193,'#skF_6')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_187)
      | ~ m1_subset_1(D_187,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_534,c_567])).

tff(c_605,plain,(
    ! [D_201,B_202] :
      ( r2_hidden(D_201,B_202)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_202)
      | ~ v13_waybel_0(B_202,'#skF_6')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_201)
      | ~ m1_subset_1(D_201,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_102,c_571])).

tff(c_613,plain,(
    ! [D_201] :
      ( r2_hidden(D_201,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_201)
      | ~ m1_subset_1(D_201,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_58,c_605])).

tff(c_619,plain,(
    ! [D_203] :
      ( r2_hidden(D_203,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_203)
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154,c_613])).

tff(c_882,plain,(
    ! [B_219] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_219),'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),B_219))
      | u1_struct_0('#skF_6') = B_219
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_619])).

tff(c_886,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_108),'#skF_7')
      | ~ l1_orders_2('#skF_6')
      | u1_struct_0('#skF_6') = B_108
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_277,c_882])).

tff(c_913,plain,(
    ! [B_221] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_221),'#skF_7')
      | u1_struct_0('#skF_6') = B_221
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_886])).

tff(c_917,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_913,c_2])).

tff(c_923,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_917])).

tff(c_190,plain,(
    ! [A_89,C_90,B_91] :
      ( m1_subset_1(A_89,C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_196,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,u1_struct_0('#skF_6'))
      | ~ r2_hidden(A_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_190])).

tff(c_248,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden('#skF_1'(A_102,B_103),B_103)
      | B_103 = A_102
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_283,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112))
      | v1_xboole_0(B_111)
      | ~ m1_subset_1('#skF_1'(A_112,B_111),B_111) ) ),
    inference(resolution,[status(thm)],[c_10,c_248])).

tff(c_296,plain,(
    ! [A_112] :
      ( u1_struct_0('#skF_6') = A_112
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_112))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_112,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_196,c_283])).

tff(c_341,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_938,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_341])).

tff(c_946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_938])).

tff(c_958,plain,(
    ! [A_224] :
      ( u1_struct_0('#skF_6') = A_224
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_224))
      | ~ r2_hidden('#skF_1'(A_224,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_961,plain,(
    ! [A_224] :
      ( u1_struct_0('#skF_6') = A_224
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_224))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_1'(A_224,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10,c_958])).

tff(c_965,plain,(
    ! [A_225] :
      ( u1_struct_0('#skF_6') = A_225
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_225))
      | ~ m1_subset_1('#skF_1'(A_225,u1_struct_0('#skF_6')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_961])).

tff(c_970,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_965])).

tff(c_971,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_970])).

tff(c_1439,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_971])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1439])).

tff(c_1451,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_153,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1458,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_153])).

tff(c_1462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_1458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.41  
% 6.26/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.41  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.26/2.41  
% 6.26/2.41  %Foreground sorts:
% 6.26/2.41  
% 6.26/2.41  
% 6.26/2.41  %Background operators:
% 6.26/2.41  
% 6.26/2.41  
% 6.26/2.41  %Foreground operators:
% 6.26/2.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.26/2.41  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 6.26/2.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.26/2.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.26/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.26/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.26/2.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.26/2.41  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.26/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.26/2.41  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.26/2.41  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 6.26/2.41  tff('#skF_7', type, '#skF_7': $i).
% 6.26/2.41  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 6.26/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.26/2.41  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 6.26/2.41  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 6.26/2.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.26/2.41  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 6.26/2.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.26/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.26/2.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.26/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.26/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.26/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.26/2.41  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.26/2.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.26/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.26/2.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.26/2.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.26/2.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.26/2.41  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 6.26/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.26/2.41  
% 6.26/2.45  tff(f_40, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 6.26/2.45  tff(f_142, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 6.26/2.45  tff(f_171, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 6.26/2.45  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 6.26/2.45  tff(f_116, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 6.26/2.45  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.26/2.45  tff(f_56, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 6.26/2.45  tff(f_60, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 6.26/2.45  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 6.26/2.45  tff(f_94, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 6.26/2.45  tff(f_135, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 6.26/2.45  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.26/2.45  tff(c_6, plain, (![A_4]: (~v1_subset_1('#skF_2'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.26/2.45  tff(c_8, plain, (![A_4]: (m1_subset_1('#skF_2'(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.26/2.45  tff(c_158, plain, (![B_84, A_85]: (v1_subset_1(B_84, A_85) | B_84=A_85 | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.26/2.45  tff(c_161, plain, (![A_4]: (v1_subset_1('#skF_2'(A_4), A_4) | '#skF_2'(A_4)=A_4)), inference(resolution, [status(thm)], [c_8, c_158])).
% 6.26/2.45  tff(c_167, plain, (![A_4]: ('#skF_2'(A_4)=A_4)), inference(negUnitSimplification, [status(thm)], [c_6, c_161])).
% 6.26/2.45  tff(c_171, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_6])).
% 6.26/2.45  tff(c_170, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_8])).
% 6.26/2.45  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_66, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_261, plain, (![A_107, B_108]: (m1_subset_1('#skF_1'(A_107, B_108), A_107) | B_108=A_107 | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.45  tff(c_40, plain, (![A_37, B_39]: (r2_lattice3(A_37, k1_xboole_0, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.26/2.45  tff(c_277, plain, (![A_37, B_108]: (r2_lattice3(A_37, k1_xboole_0, '#skF_1'(u1_struct_0(A_37), B_108)) | ~l1_orders_2(A_37) | u1_struct_0(A_37)=B_108 | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_37))))), inference(resolution, [status(thm)], [c_261, c_40])).
% 6.26/2.45  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.45  tff(c_60, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_64, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_105, plain, (![A_74, B_75]: (r2_hidden(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.45  tff(c_84, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_103, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 6.26/2.45  tff(c_108, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_105, c_103])).
% 6.26/2.45  tff(c_111, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_108])).
% 6.26/2.45  tff(c_78, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_104, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_103, c_78])).
% 6.26/2.45  tff(c_112, plain, (![B_76, A_77]: (v1_subset_1(B_76, A_77) | B_76=A_77 | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.26/2.45  tff(c_118, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_58, c_112])).
% 6.26/2.45  tff(c_124, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_104, c_118])).
% 6.26/2.45  tff(c_88, plain, (![A_71]: (k1_yellow_0(A_71, k1_xboole_0)=k3_yellow_0(A_71) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.26/2.45  tff(c_92, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_88])).
% 6.26/2.45  tff(c_97, plain, (![A_72, B_73]: (m1_subset_1(k1_yellow_0(A_72, B_73), u1_struct_0(A_72)) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.26/2.45  tff(c_100, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_92, c_97])).
% 6.26/2.45  tff(c_102, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_100])).
% 6.26/2.45  tff(c_149, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_102])).
% 6.26/2.45  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_149])).
% 6.26/2.45  tff(c_154, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 6.26/2.45  tff(c_76, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_70, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_68, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.26/2.45  tff(c_36, plain, (![A_36]: (r1_yellow_0(A_36, k1_xboole_0) | ~l1_orders_2(A_36) | ~v1_yellow_0(A_36) | ~v5_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.26/2.45  tff(c_1139, plain, (![A_283, C_284, D_285]: (r1_orders_2(A_283, k1_yellow_0(A_283, C_284), D_285) | ~r2_lattice3(A_283, C_284, D_285) | ~m1_subset_1(D_285, u1_struct_0(A_283)) | ~r1_yellow_0(A_283, C_284) | ~m1_subset_1(k1_yellow_0(A_283, C_284), u1_struct_0(A_283)) | ~l1_orders_2(A_283) | ~v5_orders_2(A_283))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.26/2.45  tff(c_1146, plain, (![D_285]: (r1_orders_2('#skF_6', k1_yellow_0('#skF_6', k1_xboole_0), D_285) | ~r2_lattice3('#skF_6', k1_xboole_0, D_285) | ~m1_subset_1(D_285, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1139])).
% 6.26/2.45  tff(c_1152, plain, (![D_285]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_285) | ~r2_lattice3('#skF_6', k1_xboole_0, D_285) | ~m1_subset_1(D_285, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_102, c_92, c_1146])).
% 6.26/2.45  tff(c_1153, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1152])).
% 6.26/2.45  tff(c_1156, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_1153])).
% 6.26/2.45  tff(c_1159, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1156])).
% 6.26/2.45  tff(c_1161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1159])).
% 6.26/2.45  tff(c_1162, plain, (![D_285]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_285) | ~r2_lattice3('#skF_6', k1_xboole_0, D_285) | ~m1_subset_1(D_285, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1152])).
% 6.26/2.45  tff(c_1195, plain, (![D_290, B_291, A_292, C_293]: (r2_hidden(D_290, B_291) | ~r1_orders_2(A_292, C_293, D_290) | ~r2_hidden(C_293, B_291) | ~m1_subset_1(D_290, u1_struct_0(A_292)) | ~m1_subset_1(C_293, u1_struct_0(A_292)) | ~v13_waybel_0(B_291, A_292) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_orders_2(A_292))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.26/2.45  tff(c_1199, plain, (![D_285, B_291]: (r2_hidden(D_285, B_291) | ~r2_hidden(k3_yellow_0('#skF_6'), B_291) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_291, '#skF_6') | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_285) | ~m1_subset_1(D_285, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1162, c_1195])).
% 6.26/2.45  tff(c_1243, plain, (![D_305, B_306]: (r2_hidden(D_305, B_306) | ~r2_hidden(k3_yellow_0('#skF_6'), B_306) | ~v13_waybel_0(B_306, '#skF_6') | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_305) | ~m1_subset_1(D_305, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_102, c_1199])).
% 6.26/2.45  tff(c_1251, plain, (![D_305]: (r2_hidden(D_305, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_305) | ~m1_subset_1(D_305, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_58, c_1243])).
% 6.26/2.45  tff(c_1257, plain, (![D_307]: (r2_hidden(D_307, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_307) | ~m1_subset_1(D_307, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154, c_1251])).
% 6.26/2.45  tff(c_1391, plain, (![B_314]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_314), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), B_314)) | u1_struct_0('#skF_6')=B_314 | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_4, c_1257])).
% 6.26/2.45  tff(c_1395, plain, (![B_108]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_108), '#skF_7') | ~l1_orders_2('#skF_6') | u1_struct_0('#skF_6')=B_108 | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_277, c_1391])).
% 6.26/2.45  tff(c_1409, plain, (![B_315]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_315), '#skF_7') | u1_struct_0('#skF_6')=B_315 | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1395])).
% 6.26/2.45  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | B_2=A_1 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.45  tff(c_1417, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1409, c_2])).
% 6.26/2.45  tff(c_1427, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1417])).
% 6.26/2.45  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.45  tff(c_511, plain, (![A_185, C_186, D_187]: (r1_orders_2(A_185, k1_yellow_0(A_185, C_186), D_187) | ~r2_lattice3(A_185, C_186, D_187) | ~m1_subset_1(D_187, u1_struct_0(A_185)) | ~r1_yellow_0(A_185, C_186) | ~m1_subset_1(k1_yellow_0(A_185, C_186), u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v5_orders_2(A_185))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.26/2.45  tff(c_518, plain, (![D_187]: (r1_orders_2('#skF_6', k1_yellow_0('#skF_6', k1_xboole_0), D_187) | ~r2_lattice3('#skF_6', k1_xboole_0, D_187) | ~m1_subset_1(D_187, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_511])).
% 6.26/2.45  tff(c_524, plain, (![D_187]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_187) | ~r2_lattice3('#skF_6', k1_xboole_0, D_187) | ~m1_subset_1(D_187, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_102, c_92, c_518])).
% 6.26/2.45  tff(c_525, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_524])).
% 6.26/2.45  tff(c_528, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_525])).
% 6.26/2.45  tff(c_531, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_528])).
% 6.26/2.45  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_531])).
% 6.26/2.45  tff(c_534, plain, (![D_187]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_187) | ~r2_lattice3('#skF_6', k1_xboole_0, D_187) | ~m1_subset_1(D_187, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_524])).
% 6.26/2.45  tff(c_567, plain, (![D_192, B_193, A_194, C_195]: (r2_hidden(D_192, B_193) | ~r1_orders_2(A_194, C_195, D_192) | ~r2_hidden(C_195, B_193) | ~m1_subset_1(D_192, u1_struct_0(A_194)) | ~m1_subset_1(C_195, u1_struct_0(A_194)) | ~v13_waybel_0(B_193, A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_orders_2(A_194))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.26/2.45  tff(c_571, plain, (![D_187, B_193]: (r2_hidden(D_187, B_193) | ~r2_hidden(k3_yellow_0('#skF_6'), B_193) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_193, '#skF_6') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_187) | ~m1_subset_1(D_187, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_534, c_567])).
% 6.26/2.45  tff(c_605, plain, (![D_201, B_202]: (r2_hidden(D_201, B_202) | ~r2_hidden(k3_yellow_0('#skF_6'), B_202) | ~v13_waybel_0(B_202, '#skF_6') | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_201) | ~m1_subset_1(D_201, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_102, c_571])).
% 6.26/2.45  tff(c_613, plain, (![D_201]: (r2_hidden(D_201, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_201) | ~m1_subset_1(D_201, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_58, c_605])).
% 6.26/2.45  tff(c_619, plain, (![D_203]: (r2_hidden(D_203, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_203) | ~m1_subset_1(D_203, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154, c_613])).
% 6.26/2.45  tff(c_882, plain, (![B_219]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_219), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), B_219)) | u1_struct_0('#skF_6')=B_219 | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_4, c_619])).
% 6.26/2.45  tff(c_886, plain, (![B_108]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_108), '#skF_7') | ~l1_orders_2('#skF_6') | u1_struct_0('#skF_6')=B_108 | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(resolution, [status(thm)], [c_277, c_882])).
% 6.26/2.45  tff(c_913, plain, (![B_221]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_221), '#skF_7') | u1_struct_0('#skF_6')=B_221 | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_886])).
% 6.26/2.45  tff(c_917, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_913, c_2])).
% 6.26/2.45  tff(c_923, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_917])).
% 6.26/2.45  tff(c_190, plain, (![A_89, C_90, B_91]: (m1_subset_1(A_89, C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.26/2.45  tff(c_196, plain, (![A_89]: (m1_subset_1(A_89, u1_struct_0('#skF_6')) | ~r2_hidden(A_89, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_190])).
% 6.26/2.45  tff(c_248, plain, (![A_102, B_103]: (~r2_hidden('#skF_1'(A_102, B_103), B_103) | B_103=A_102 | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.45  tff(c_283, plain, (![B_111, A_112]: (B_111=A_112 | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)) | v1_xboole_0(B_111) | ~m1_subset_1('#skF_1'(A_112, B_111), B_111))), inference(resolution, [status(thm)], [c_10, c_248])).
% 6.26/2.45  tff(c_296, plain, (![A_112]: (u1_struct_0('#skF_6')=A_112 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_112)) | v1_xboole_0(u1_struct_0('#skF_6')) | ~r2_hidden('#skF_1'(A_112, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_196, c_283])).
% 6.26/2.45  tff(c_341, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_296])).
% 6.26/2.45  tff(c_938, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_923, c_341])).
% 6.26/2.45  tff(c_946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_938])).
% 6.26/2.45  tff(c_958, plain, (![A_224]: (u1_struct_0('#skF_6')=A_224 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_224)) | ~r2_hidden('#skF_1'(A_224, u1_struct_0('#skF_6')), '#skF_7'))), inference(splitRight, [status(thm)], [c_296])).
% 6.26/2.45  tff(c_961, plain, (![A_224]: (u1_struct_0('#skF_6')=A_224 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_224)) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_1'(A_224, u1_struct_0('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_10, c_958])).
% 6.26/2.45  tff(c_965, plain, (![A_225]: (u1_struct_0('#skF_6')=A_225 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_225)) | ~m1_subset_1('#skF_1'(A_225, u1_struct_0('#skF_6')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_961])).
% 6.26/2.45  tff(c_970, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_965])).
% 6.26/2.45  tff(c_971, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_970])).
% 6.26/2.45  tff(c_1439, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_971])).
% 6.26/2.45  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_1439])).
% 6.26/2.45  tff(c_1451, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_970])).
% 6.26/2.45  tff(c_153, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 6.26/2.45  tff(c_1458, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_153])).
% 6.26/2.45  tff(c_1462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_1458])).
% 6.26/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.45  
% 6.26/2.45  Inference rules
% 6.26/2.45  ----------------------
% 6.26/2.45  #Ref     : 0
% 6.26/2.45  #Sup     : 225
% 6.26/2.45  #Fact    : 0
% 6.26/2.45  #Define  : 0
% 6.26/2.45  #Split   : 9
% 6.26/2.45  #Chain   : 0
% 6.26/2.45  #Close   : 0
% 6.26/2.45  
% 6.26/2.45  Ordering : KBO
% 6.26/2.45  
% 6.26/2.45  Simplification rules
% 6.26/2.45  ----------------------
% 6.26/2.45  #Subsume      : 25
% 6.26/2.45  #Demod        : 309
% 6.26/2.45  #Tautology    : 68
% 6.26/2.45  #SimpNegUnit  : 19
% 6.26/2.45  #BackRed      : 72
% 6.26/2.45  
% 6.26/2.45  #Partial instantiations: 0
% 6.26/2.45  #Strategies tried      : 1
% 6.26/2.45  
% 6.26/2.45  Timing (in seconds)
% 6.26/2.45  ----------------------
% 6.26/2.45  Preprocessing        : 0.58
% 6.26/2.45  Parsing              : 0.29
% 6.26/2.45  CNF conversion       : 0.05
% 6.26/2.45  Main loop            : 1.00
% 6.26/2.45  Inferencing          : 0.39
% 6.26/2.45  Reduction            : 0.29
% 6.26/2.45  Demodulation         : 0.20
% 6.26/2.45  BG Simplification    : 0.05
% 6.26/2.45  Subsumption          : 0.17
% 6.26/2.45  Abstraction          : 0.04
% 6.26/2.45  MUC search           : 0.00
% 6.26/2.46  Cooper               : 0.00
% 6.26/2.46  Total                : 1.65
% 6.26/2.46  Index Insertion      : 0.00
% 6.26/2.46  Index Deletion       : 0.00
% 6.26/2.46  Index Matching       : 0.00
% 6.26/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
