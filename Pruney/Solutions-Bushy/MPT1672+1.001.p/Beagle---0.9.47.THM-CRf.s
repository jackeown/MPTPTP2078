%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1672+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:13 EST 2020

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 257 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :   31
%              Number of atoms          :  382 (1629 expanded)
%              Number of equality atoms :   21 ( 160 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r1_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r1_yellow_0(A,E)
                                    & D = k1_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k1_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,B,D)
                      <=> r2_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

tff(f_63,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
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

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_56,axiom,(
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
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_70,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_108,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r2_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_110,plain,(
    ! [A_131,C_132,B_133] :
      ( m1_subset_1(A_131,C_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(C_132))
      | ~ r2_hidden(A_131,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_118,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_131,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_27] : v1_finset_1(k1_tarski(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_146,plain,(
    ! [D_142] :
      ( r1_yellow_0('#skF_3',D_142)
      | k1_xboole_0 = D_142
      | ~ m1_subset_1(D_142,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_151,plain,(
    ! [A_45] :
      ( r1_yellow_0('#skF_3',A_45)
      | k1_xboole_0 = A_45
      | ~ v1_finset_1(A_45)
      | ~ r1_tarski(A_45,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_54,plain,(
    ! [D_117] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_117),'#skF_5')
      | k1_xboole_0 = D_117
      | ~ m1_subset_1(D_117,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_119,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_110])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k1_yellow_0(A_25,B_26),u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_445,plain,(
    ! [A_200,B_201] :
      ( r2_lattice3(A_200,B_201,k1_yellow_0(A_200,B_201))
      | ~ r1_yellow_0(A_200,B_201)
      | ~ m1_subset_1(k1_yellow_0(A_200,B_201),u1_struct_0(A_200))
      | ~ l1_orders_2(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_470,plain,(
    ! [A_25,B_26] :
      ( r2_lattice3(A_25,B_26,k1_yellow_0(A_25,B_26))
      | ~ r1_yellow_0(A_25,B_26)
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_445])).

tff(c_480,plain,(
    ! [A_204,C_205,B_206] :
      ( r1_orders_2(A_204,C_205,B_206)
      | ~ r2_lattice3(A_204,k1_tarski(C_205),B_206)
      | ~ m1_subset_1(C_205,u1_struct_0(A_204))
      | ~ m1_subset_1(B_206,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2374,plain,(
    ! [A_465,C_466] :
      ( r1_orders_2(A_465,C_466,k1_yellow_0(A_465,k1_tarski(C_466)))
      | ~ m1_subset_1(C_466,u1_struct_0(A_465))
      | ~ m1_subset_1(k1_yellow_0(A_465,k1_tarski(C_466)),u1_struct_0(A_465))
      | ~ r1_yellow_0(A_465,k1_tarski(C_466))
      | ~ l1_orders_2(A_465) ) ),
    inference(resolution,[status(thm)],[c_470,c_480])).

tff(c_2380,plain,(
    ! [C_466] :
      ( r1_orders_2('#skF_3',C_466,k1_yellow_0('#skF_3',k1_tarski(C_466)))
      | ~ m1_subset_1(C_466,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_466))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_466)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_2374])).

tff(c_2413,plain,(
    ! [C_469] :
      ( r1_orders_2('#skF_3',C_469,k1_yellow_0('#skF_3',k1_tarski(C_469)))
      | ~ m1_subset_1(C_469,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_469))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_469)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2380])).

tff(c_64,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_76,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_109,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_76])).

tff(c_245,plain,(
    ! [A_157,B_158,D_159,C_160] :
      ( r2_lattice3(A_157,B_158,D_159)
      | ~ r2_lattice3(A_157,C_160,D_159)
      | ~ m1_subset_1(D_159,u1_struct_0(A_157))
      | ~ r1_tarski(B_158,C_160)
      | ~ l1_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_247,plain,(
    ! [B_158] :
      ( r2_lattice3('#skF_3',B_158,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_158,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_109,c_245])).

tff(c_250,plain,(
    ! [B_158] :
      ( r2_lattice3('#skF_3',B_158,'#skF_7')
      | ~ r1_tarski(B_158,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_247])).

tff(c_500,plain,(
    ! [C_205] :
      ( r1_orders_2('#skF_3',C_205,'#skF_7')
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_205),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_250,c_480])).

tff(c_560,plain,(
    ! [C_211] :
      ( r1_orders_2('#skF_3',C_211,'#skF_7')
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_211),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_500])).

tff(c_566,plain,(
    ! [A_212] :
      ( r1_orders_2('#skF_3',A_212,'#skF_7')
      | ~ m1_subset_1(A_212,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_212,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_560])).

tff(c_594,plain,(
    ! [A_131] :
      ( r1_orders_2('#skF_3',A_131,'#skF_7')
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_566])).

tff(c_1572,plain,(
    ! [A_360,B_361,D_362,C_363] :
      ( r1_orders_2(A_360,B_361,D_362)
      | ~ r1_orders_2(A_360,C_363,D_362)
      | ~ r1_orders_2(A_360,B_361,C_363)
      | ~ m1_subset_1(D_362,u1_struct_0(A_360))
      | ~ m1_subset_1(C_363,u1_struct_0(A_360))
      | ~ m1_subset_1(B_361,u1_struct_0(A_360))
      | ~ l1_orders_2(A_360)
      | ~ v4_orders_2(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1592,plain,(
    ! [B_361,A_131] :
      ( r1_orders_2('#skF_3',B_361,'#skF_7')
      | ~ r1_orders_2('#skF_3',B_361,A_131)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_594,c_1572])).

tff(c_1618,plain,(
    ! [B_361,A_131] :
      ( r1_orders_2('#skF_3',B_361,'#skF_7')
      | ~ r1_orders_2('#skF_3',B_361,A_131)
      | ~ m1_subset_1(A_131,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_131,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_1592])).

tff(c_3910,plain,(
    ! [C_670] :
      ( r1_orders_2('#skF_3',C_670,'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',k1_tarski(C_670)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_670,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_670))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_670)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2413,c_1618])).

tff(c_3952,plain,(
    ! [C_674] :
      ( r1_orders_2('#skF_3',C_674,'#skF_7')
      | ~ m1_subset_1(C_674,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_674))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_674)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_119,c_3910])).

tff(c_3955,plain,(
    ! [C_674] :
      ( r1_orders_2('#skF_3',C_674,'#skF_7')
      | ~ m1_subset_1(C_674,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_674))
      | k1_tarski(C_674) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_674),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(C_674)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3952])).

tff(c_4146,plain,(
    ! [C_677] :
      ( r1_orders_2('#skF_3',C_677,'#skF_7')
      | ~ m1_subset_1(C_677,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_677))
      | k1_tarski(C_677) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_677),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3955])).

tff(c_4308,plain,(
    ! [C_686] :
      ( r1_orders_2('#skF_3',C_686,'#skF_7')
      | ~ m1_subset_1(C_686,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_686))
      | k1_tarski(C_686) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_686),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_4146])).

tff(c_4311,plain,(
    ! [C_686] :
      ( r1_orders_2('#skF_3',C_686,'#skF_7')
      | ~ m1_subset_1(C_686,u1_struct_0('#skF_3'))
      | k1_tarski(C_686) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(C_686))
      | ~ r1_tarski(k1_tarski(C_686),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_4308])).

tff(c_4315,plain,(
    ! [C_687] :
      ( r1_orders_2('#skF_3',C_687,'#skF_7')
      | ~ m1_subset_1(C_687,u1_struct_0('#skF_3'))
      | k1_tarski(C_687) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_687),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4311])).

tff(c_4321,plain,(
    ! [A_688] :
      ( r1_orders_2('#skF_3',A_688,'#skF_7')
      | ~ m1_subset_1(A_688,u1_struct_0('#skF_3'))
      | k1_tarski(A_688) = k1_xboole_0
      | ~ r2_hidden(A_688,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_4315])).

tff(c_4368,plain,(
    ! [A_689] :
      ( r1_orders_2('#skF_3',A_689,'#skF_7')
      | k1_tarski(A_689) = k1_xboole_0
      | ~ r2_hidden(A_689,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_118,c_4321])).

tff(c_4,plain,(
    ! [A_1,B_8,C_9] :
      ( ~ r1_orders_2(A_1,'#skF_1'(A_1,B_8,C_9),C_9)
      | r2_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4380,plain,(
    ! [B_8] :
      ( r2_lattice3('#skF_3',B_8,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_8,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_8,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4368,c_4])).

tff(c_4396,plain,(
    ! [B_690] :
      ( r2_lattice3('#skF_3',B_690,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_690,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_690,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_4380])).

tff(c_4400,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_4396])).

tff(c_4403,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_4400])).

tff(c_4404,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4403])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r2_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_213,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_1'(A_151,B_152,C_153),B_152)
      | r2_lattice3(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [B_51,A_50] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_226,plain,(
    ! [B_154,A_155,C_156] :
      ( ~ v1_xboole_0(B_154)
      | r2_lattice3(A_155,B_154,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(resolution,[status(thm)],[c_213,c_38])).

tff(c_234,plain,(
    ! [B_154] :
      ( ~ v1_xboole_0(B_154)
      | r2_lattice3('#skF_3',B_154,'#skF_7')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_226])).

tff(c_244,plain,(
    ! [B_154] :
      ( ~ v1_xboole_0(B_154)
      | r2_lattice3('#skF_3',B_154,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_234])).

tff(c_504,plain,(
    ! [C_205] :
      ( r1_orders_2('#skF_3',C_205,'#skF_7')
      | ~ m1_subset_1(C_205,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v1_xboole_0(k1_tarski(C_205)) ) ),
    inference(resolution,[status(thm)],[c_244,c_480])).

tff(c_519,plain,(
    ! [C_207] :
      ( r1_orders_2('#skF_3',C_207,'#skF_7')
      | ~ m1_subset_1(C_207,u1_struct_0('#skF_3'))
      | ~ v1_xboole_0(k1_tarski(C_207)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_504])).

tff(c_523,plain,(
    ! [B_8,C_9] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_8,C_9),'#skF_7')
      | ~ v1_xboole_0(k1_tarski('#skF_1'('#skF_3',B_8,C_9)))
      | r2_lattice3('#skF_3',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_519])).

tff(c_543,plain,(
    ! [B_8,C_9] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_8,C_9),'#skF_7')
      | ~ v1_xboole_0(k1_tarski('#skF_1'('#skF_3',B_8,C_9)))
      | r2_lattice3('#skF_3',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_523])).

tff(c_4502,plain,
    ( r1_orders_2('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_7'),'#skF_7')
    | ~ v1_xboole_0(k1_xboole_0)
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4404,c_543])).

tff(c_4566,plain,
    ( r1_orders_2('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_7'),'#skF_7')
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24,c_4502])).

tff(c_4567,plain,(
    r1_orders_2('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4566])).

tff(c_4619,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_4567,c_4])).

tff(c_4634,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_4619])).

tff(c_4636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_4634])).

tff(c_4637,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4654,plain,(
    ! [A_694,C_695,B_696] :
      ( m1_subset_1(A_694,C_695)
      | ~ m1_subset_1(B_696,k1_zfmisc_1(C_695))
      | ~ r2_hidden(A_694,B_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4663,plain,(
    ! [A_694] :
      ( m1_subset_1(A_694,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_694,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4654])).

tff(c_4704,plain,(
    ! [D_707] :
      ( m1_subset_1('#skF_6'(D_707),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_707,'#skF_5')
      | ~ m1_subset_1(D_707,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4715,plain,(
    ! [D_707] :
      ( r1_tarski('#skF_6'(D_707),'#skF_4')
      | ~ r2_hidden(D_707,'#skF_5')
      | ~ m1_subset_1(D_707,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4704,c_32])).

tff(c_80,plain,(
    ! [D_115] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_115))
      | ~ r2_hidden(D_115,'#skF_5')
      | ~ m1_subset_1(D_115,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4639,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4637,c_76])).

tff(c_4757,plain,(
    ! [A_716,B_717,D_718,C_719] :
      ( r2_lattice3(A_716,B_717,D_718)
      | ~ r2_lattice3(A_716,C_719,D_718)
      | ~ m1_subset_1(D_718,u1_struct_0(A_716))
      | ~ r1_tarski(B_717,C_719)
      | ~ l1_orders_2(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4759,plain,(
    ! [B_717] :
      ( r2_lattice3('#skF_3',B_717,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_717,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4639,c_4757])).

tff(c_4762,plain,(
    ! [B_717] :
      ( r2_lattice3('#skF_3',B_717,'#skF_7')
      | ~ r1_tarski(B_717,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_4759])).

tff(c_4684,plain,(
    ! [D_706] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_706)) = D_706
      | ~ r2_hidden(D_706,'#skF_5')
      | ~ m1_subset_1(D_706,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4698,plain,(
    ! [A_694] :
      ( k1_yellow_0('#skF_3','#skF_6'(A_694)) = A_694
      | ~ r2_hidden(A_694,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4663,c_4684])).

tff(c_5878,plain,(
    ! [A_906,B_907,D_908] :
      ( r1_orders_2(A_906,k1_yellow_0(A_906,B_907),D_908)
      | ~ r2_lattice3(A_906,B_907,D_908)
      | ~ m1_subset_1(D_908,u1_struct_0(A_906))
      | ~ r1_yellow_0(A_906,B_907)
      | ~ m1_subset_1(k1_yellow_0(A_906,B_907),u1_struct_0(A_906))
      | ~ l1_orders_2(A_906) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5915,plain,(
    ! [A_911,B_912,D_913] :
      ( r1_orders_2(A_911,k1_yellow_0(A_911,B_912),D_913)
      | ~ r2_lattice3(A_911,B_912,D_913)
      | ~ m1_subset_1(D_913,u1_struct_0(A_911))
      | ~ r1_yellow_0(A_911,B_912)
      | ~ l1_orders_2(A_911) ) ),
    inference(resolution,[status(thm)],[c_20,c_5878])).

tff(c_5922,plain,(
    ! [A_694,D_913] :
      ( r1_orders_2('#skF_3',A_694,D_913)
      | ~ r2_lattice3('#skF_3','#skF_6'(A_694),D_913)
      | ~ m1_subset_1(D_913,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_694))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_694,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4698,c_5915])).

tff(c_5933,plain,(
    ! [A_917,D_918] :
      ( r1_orders_2('#skF_3',A_917,D_918)
      | ~ r2_lattice3('#skF_3','#skF_6'(A_917),D_918)
      | ~ m1_subset_1(D_918,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_917))
      | ~ r2_hidden(A_917,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5922])).

tff(c_6003,plain,(
    ! [A_917] :
      ( r1_orders_2('#skF_3',A_917,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_917))
      | ~ r2_hidden(A_917,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_917),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4762,c_5933])).

tff(c_6179,plain,(
    ! [A_929] :
      ( r1_orders_2('#skF_3',A_929,'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'(A_929))
      | ~ r2_hidden(A_929,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_929),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6003])).

tff(c_6188,plain,(
    ! [D_930] :
      ( r1_orders_2('#skF_3',D_930,'#skF_7')
      | ~ r1_tarski('#skF_6'(D_930),'#skF_4')
      | ~ r2_hidden(D_930,'#skF_5')
      | ~ m1_subset_1(D_930,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_80,c_6179])).

tff(c_6193,plain,(
    ! [D_931] :
      ( r1_orders_2('#skF_3',D_931,'#skF_7')
      | ~ r2_hidden(D_931,'#skF_5')
      | ~ m1_subset_1(D_931,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4715,c_6188])).

tff(c_6252,plain,(
    ! [A_936] :
      ( r1_orders_2('#skF_3',A_936,'#skF_7')
      | ~ r2_hidden(A_936,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4663,c_6193])).

tff(c_6258,plain,(
    ! [B_8] :
      ( r2_lattice3('#skF_3',B_8,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_8,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6252,c_4])).

tff(c_6265,plain,(
    ! [B_937] :
      ( r2_lattice3('#skF_3',B_937,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_937,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_6258])).

tff(c_6269,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_6265])).

tff(c_6272,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_6269])).

tff(c_6274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4637,c_6272])).

%------------------------------------------------------------------------------
