%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:52 EST 2020

% Result     : Theorem 26.39s
% Output     : CNFRefutation 26.82s
% Verified   : 
% Statistics : Number of formulae       :  358 (10434 expanded)
%              Number of leaves         :   37 (4082 expanded)
%              Depth                    :   45
%              Number of atoms          : 2256 (60527 expanded)
%              Number of equality atoms :  296 (8817 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_215,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( r2_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                      | ( r1_orders_2(A,B,C)
                        & r2_orders_2(A,C,D) ) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_46,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_42,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_40,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_57624,plain,(
    ! [C_4232,A_4233,B_4234] :
      ( m1_subset_1(C_4232,k1_zfmisc_1(u1_struct_0(A_4233)))
      | ~ m2_orders_2(C_4232,A_4233,B_4234)
      | ~ m1_orders_1(B_4234,k1_orders_1(u1_struct_0(A_4233)))
      | ~ l1_orders_2(A_4233)
      | ~ v5_orders_2(A_4233)
      | ~ v4_orders_2(A_4233)
      | ~ v3_orders_2(A_4233)
      | v2_struct_0(A_4233) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57626,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_57624])).

tff(c_57629,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_42,c_57626])).

tff(c_57630,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_57629])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k3_orders_2(A_14,B_15,C_16),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57633,plain,(
    ! [A_4] :
      ( m1_subset_1(A_4,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_4,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57630,c_6])).

tff(c_38,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58078,plain,(
    ! [A_4325,D_4326,B_4327,E_4328] :
      ( r3_orders_2(A_4325,k1_funct_1(D_4326,u1_struct_0(A_4325)),B_4327)
      | ~ r2_hidden(B_4327,E_4328)
      | ~ m2_orders_2(E_4328,A_4325,D_4326)
      | ~ m1_orders_1(D_4326,k1_orders_1(u1_struct_0(A_4325)))
      | ~ m1_subset_1(k1_funct_1(D_4326,u1_struct_0(A_4325)),u1_struct_0(A_4325))
      | ~ m1_subset_1(B_4327,u1_struct_0(A_4325))
      | ~ l1_orders_2(A_4325)
      | ~ v5_orders_2(A_4325)
      | ~ v4_orders_2(A_4325)
      | ~ v3_orders_2(A_4325)
      | v2_struct_0(A_4325) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58202,plain,(
    ! [A_4358,D_4359,A_4360,B_4361] :
      ( r3_orders_2(A_4358,k1_funct_1(D_4359,u1_struct_0(A_4358)),'#skF_1'(A_4360,B_4361))
      | ~ m2_orders_2(B_4361,A_4358,D_4359)
      | ~ m1_orders_1(D_4359,k1_orders_1(u1_struct_0(A_4358)))
      | ~ m1_subset_1(k1_funct_1(D_4359,u1_struct_0(A_4358)),u1_struct_0(A_4358))
      | ~ m1_subset_1('#skF_1'(A_4360,B_4361),u1_struct_0(A_4358))
      | ~ l1_orders_2(A_4358)
      | ~ v5_orders_2(A_4358)
      | ~ v4_orders_2(A_4358)
      | ~ v3_orders_2(A_4358)
      | v2_struct_0(A_4358)
      | k1_xboole_0 = B_4361
      | ~ m1_subset_1(B_4361,k1_zfmisc_1(A_4360)) ) ),
    inference(resolution,[status(thm)],[c_2,c_58078])).

tff(c_58207,plain,(
    ! [A_4360,B_4361] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4360,B_4361))
      | ~ m2_orders_2(B_4361,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_4360,B_4361),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_4361
      | ~ m1_subset_1(B_4361,k1_zfmisc_1(A_4360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_58202])).

tff(c_58210,plain,(
    ! [A_4360,B_4361] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4360,B_4361))
      | ~ m2_orders_2(B_4361,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_4360,B_4361),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_4361
      | ~ m1_subset_1(B_4361,k1_zfmisc_1(A_4360)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_58207])).

tff(c_58212,plain,(
    ! [A_4362,B_4363] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4362,B_4363))
      | ~ m2_orders_2(B_4363,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_4362,B_4363),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_4363
      | ~ m1_subset_1(B_4363,k1_zfmisc_1(A_4362)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_58210])).

tff(c_58257,plain,(
    ! [A_4369,B_4370] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4369,B_4370))
      | ~ m2_orders_2(B_4370,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4370
      | ~ m1_subset_1(B_4370,k1_zfmisc_1(A_4369))
      | ~ r2_hidden('#skF_1'(A_4369,B_4370),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57633,c_58212])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_orders_2(A_21,B_22,C_23)
      | ~ r3_orders_2(A_21,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_21))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21)
      | ~ v3_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58259,plain,(
    ! [A_4369,B_4370] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4369,B_4370))
      | ~ m1_subset_1('#skF_1'(A_4369,B_4370),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4370,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4370
      | ~ m1_subset_1(B_4370,k1_zfmisc_1(A_4369))
      | ~ r2_hidden('#skF_1'(A_4369,B_4370),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58257,c_22])).

tff(c_58262,plain,(
    ! [A_4369,B_4370] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4369,B_4370))
      | ~ m1_subset_1('#skF_1'(A_4369,B_4370),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4370,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4370
      | ~ m1_subset_1(B_4370,k1_zfmisc_1(A_4369))
      | ~ r2_hidden('#skF_1'(A_4369,B_4370),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_58259])).

tff(c_58287,plain,(
    ! [A_4372,B_4373] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4372,B_4373))
      | ~ m1_subset_1('#skF_1'(A_4372,B_4373),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_4373,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4373
      | ~ m1_subset_1(B_4373,k1_zfmisc_1(A_4372))
      | ~ r2_hidden('#skF_1'(A_4372,B_4373),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_58262])).

tff(c_58336,plain,(
    ! [A_4375,B_4376] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4375,B_4376))
      | ~ m2_orders_2(B_4376,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4376
      | ~ m1_subset_1(B_4376,k1_zfmisc_1(A_4375))
      | ~ r2_hidden('#skF_1'(A_4375,B_4376),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57633,c_58287])).

tff(c_57634,plain,(
    ! [A_4235] :
      ( m1_subset_1(A_4235,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_4235,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57630,c_6])).

tff(c_74,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_orders_2(A_111,B_112,C_113)
      | C_113 = B_112
      | ~ r1_orders_2(A_111,B_112,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [B_112] :
      ( r2_orders_2('#skF_2',B_112,'#skF_3')
      | B_112 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_112,'#skF_3')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_83,plain,(
    ! [B_112] :
      ( r2_orders_2('#skF_2',B_112,'#skF_3')
      | B_112 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_112,'#skF_3')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_57650,plain,(
    ! [A_4235] :
      ( r2_orders_2('#skF_2',A_4235,'#skF_3')
      | A_4235 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_4235,'#skF_3')
      | ~ r2_hidden(A_4235,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57634,c_83])).

tff(c_57802,plain,(
    ! [A_4266,C_4267,D_4268,B_4269] :
      ( ~ r2_orders_2(A_4266,C_4267,D_4268)
      | ~ r1_orders_2(A_4266,B_4269,C_4267)
      | r2_orders_2(A_4266,B_4269,D_4268)
      | ~ m1_subset_1(D_4268,u1_struct_0(A_4266))
      | ~ m1_subset_1(C_4267,u1_struct_0(A_4266))
      | ~ m1_subset_1(B_4269,u1_struct_0(A_4266))
      | ~ l1_orders_2(A_4266)
      | ~ v5_orders_2(A_4266)
      | ~ v4_orders_2(A_4266) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_57810,plain,(
    ! [B_4269,A_4235] :
      ( ~ r1_orders_2('#skF_2',B_4269,A_4235)
      | r2_orders_2('#skF_2',B_4269,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_4235,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4269,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_4235 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_4235,'#skF_3')
      | ~ r2_hidden(A_4235,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_57650,c_57802])).

tff(c_57824,plain,(
    ! [B_4269,A_4235] :
      ( ~ r1_orders_2('#skF_2',B_4269,A_4235)
      | r2_orders_2('#skF_2',B_4269,'#skF_3')
      | ~ m1_subset_1(A_4235,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4269,u1_struct_0('#skF_2'))
      | A_4235 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_4235,'#skF_3')
      | ~ r2_hidden(A_4235,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_57810])).

tff(c_58345,plain,(
    ! [A_4375,B_4376] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_4375,B_4376),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | '#skF_1'(A_4375,B_4376) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_4375,B_4376),'#skF_3')
      | ~ m2_orders_2(B_4376,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4376
      | ~ m1_subset_1(B_4376,k1_zfmisc_1(A_4375))
      | ~ r2_hidden('#skF_1'(A_4375,B_4376),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58336,c_57824])).

tff(c_58359,plain,(
    ! [A_4375,B_4376] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_4375,B_4376),u1_struct_0('#skF_2'))
      | '#skF_1'(A_4375,B_4376) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_4375,B_4376),'#skF_3')
      | ~ m2_orders_2(B_4376,'#skF_2','#skF_4')
      | k1_xboole_0 = B_4376
      | ~ m1_subset_1(B_4376,k1_zfmisc_1(A_4375))
      | ~ r2_hidden('#skF_1'(A_4375,B_4376),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58345])).

tff(c_58570,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58359])).

tff(c_10,plain,(
    ! [A_7,C_13] :
      ( ~ r2_orders_2(A_7,C_13,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58576,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_58570,c_10])).

tff(c_58586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_58576])).

tff(c_58588,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58359])).

tff(c_57685,plain,(
    ! [A_4240,B_4241,C_4242] :
      ( m1_subset_1(k3_orders_2(A_4240,B_4241,C_4242),k1_zfmisc_1(u1_struct_0(A_4240)))
      | ~ m1_subset_1(C_4242,u1_struct_0(A_4240))
      | ~ m1_subset_1(B_4241,k1_zfmisc_1(u1_struct_0(A_4240)))
      | ~ l1_orders_2(A_4240)
      | ~ v5_orders_2(A_4240)
      | ~ v4_orders_2(A_4240)
      | ~ v3_orders_2(A_4240)
      | v2_struct_0(A_4240) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_57778,plain,(
    ! [A_4256,A_4257,B_4258,C_4259] :
      ( m1_subset_1(A_4256,u1_struct_0(A_4257))
      | ~ r2_hidden(A_4256,k3_orders_2(A_4257,B_4258,C_4259))
      | ~ m1_subset_1(C_4259,u1_struct_0(A_4257))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0(A_4257)))
      | ~ l1_orders_2(A_4257)
      | ~ v5_orders_2(A_4257)
      | ~ v4_orders_2(A_4257)
      | ~ v3_orders_2(A_4257)
      | v2_struct_0(A_4257) ) ),
    inference(resolution,[status(thm)],[c_57685,c_6])).

tff(c_57782,plain,(
    ! [A_1,A_4257,B_4258,C_4259] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2(A_4257,B_4258,C_4259)),u1_struct_0(A_4257))
      | ~ m1_subset_1(C_4259,u1_struct_0(A_4257))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0(A_4257)))
      | ~ l1_orders_2(A_4257)
      | ~ v5_orders_2(A_4257)
      | ~ v4_orders_2(A_4257)
      | ~ v3_orders_2(A_4257)
      | v2_struct_0(A_4257)
      | k3_orders_2(A_4257,B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4257,B_4258,C_4259),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_57778])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57941,plain,(
    ! [B_4284,D_4285,A_4286,C_4287] :
      ( r2_hidden(B_4284,D_4285)
      | ~ r2_hidden(B_4284,k3_orders_2(A_4286,D_4285,C_4287))
      | ~ m1_subset_1(D_4285,k1_zfmisc_1(u1_struct_0(A_4286)))
      | ~ m1_subset_1(C_4287,u1_struct_0(A_4286))
      | ~ m1_subset_1(B_4284,u1_struct_0(A_4286))
      | ~ l1_orders_2(A_4286)
      | ~ v5_orders_2(A_4286)
      | ~ v4_orders_2(A_4286)
      | ~ v3_orders_2(A_4286)
      | v2_struct_0(A_4286) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58235,plain,(
    ! [A_4364,A_4365,D_4366,C_4367] :
      ( r2_hidden('#skF_1'(A_4364,k3_orders_2(A_4365,D_4366,C_4367)),D_4366)
      | ~ m1_subset_1(D_4366,k1_zfmisc_1(u1_struct_0(A_4365)))
      | ~ m1_subset_1(C_4367,u1_struct_0(A_4365))
      | ~ m1_subset_1('#skF_1'(A_4364,k3_orders_2(A_4365,D_4366,C_4367)),u1_struct_0(A_4365))
      | ~ l1_orders_2(A_4365)
      | ~ v5_orders_2(A_4365)
      | ~ v4_orders_2(A_4365)
      | ~ v3_orders_2(A_4365)
      | v2_struct_0(A_4365)
      | k3_orders_2(A_4365,D_4366,C_4367) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4365,D_4366,C_4367),k1_zfmisc_1(A_4364)) ) ),
    inference(resolution,[status(thm)],[c_2,c_57941])).

tff(c_58483,plain,(
    ! [A_4391,D_4392,C_4393] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_4391),k3_orders_2(A_4391,D_4392,C_4393)),D_4392)
      | ~ m1_subset_1(D_4392,k1_zfmisc_1(u1_struct_0(A_4391)))
      | ~ m1_subset_1(C_4393,u1_struct_0(A_4391))
      | ~ l1_orders_2(A_4391)
      | ~ v5_orders_2(A_4391)
      | ~ v4_orders_2(A_4391)
      | ~ v3_orders_2(A_4391)
      | v2_struct_0(A_4391)
      | k3_orders_2(A_4391,D_4392,C_4393) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4391,D_4392,C_4393),k1_zfmisc_1(u1_struct_0(A_4391))) ) ),
    inference(resolution,[status(thm)],[c_4,c_58235])).

tff(c_34,plain,(
    ! [A_54,D_82,B_70,E_84] :
      ( r3_orders_2(A_54,k1_funct_1(D_82,u1_struct_0(A_54)),B_70)
      | ~ r2_hidden(B_70,E_84)
      | ~ m2_orders_2(E_84,A_54,D_82)
      | ~ m1_orders_1(D_82,k1_orders_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(k1_funct_1(D_82,u1_struct_0(A_54)),u1_struct_0(A_54))
      | ~ m1_subset_1(B_70,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_73570,plain,(
    ! [C_5511,A_5510,D_5509,A_5512,D_5508] :
      ( r3_orders_2(A_5510,k1_funct_1(D_5509,u1_struct_0(A_5510)),'#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)))
      | ~ m2_orders_2(D_5508,A_5510,D_5509)
      | ~ m1_orders_1(D_5509,k1_orders_1(u1_struct_0(A_5510)))
      | ~ m1_subset_1(k1_funct_1(D_5509,u1_struct_0(A_5510)),u1_struct_0(A_5510))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)),u1_struct_0(A_5510))
      | ~ l1_orders_2(A_5510)
      | ~ v5_orders_2(A_5510)
      | ~ v4_orders_2(A_5510)
      | ~ v3_orders_2(A_5510)
      | v2_struct_0(A_5510)
      | ~ m1_subset_1(D_5508,k1_zfmisc_1(u1_struct_0(A_5512)))
      | ~ m1_subset_1(C_5511,u1_struct_0(A_5512))
      | ~ l1_orders_2(A_5512)
      | ~ v5_orders_2(A_5512)
      | ~ v4_orders_2(A_5512)
      | ~ v3_orders_2(A_5512)
      | v2_struct_0(A_5512)
      | k3_orders_2(A_5512,D_5508,C_5511) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_5512,D_5508,C_5511),k1_zfmisc_1(u1_struct_0(A_5512))) ) ),
    inference(resolution,[status(thm)],[c_58483,c_34])).

tff(c_73578,plain,(
    ! [A_5512,D_5508,C_5511] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)))
      | ~ m2_orders_2(D_5508,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_5508,k1_zfmisc_1(u1_struct_0(A_5512)))
      | ~ m1_subset_1(C_5511,u1_struct_0(A_5512))
      | ~ l1_orders_2(A_5512)
      | ~ v5_orders_2(A_5512)
      | ~ v4_orders_2(A_5512)
      | ~ v3_orders_2(A_5512)
      | v2_struct_0(A_5512)
      | k3_orders_2(A_5512,D_5508,C_5511) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_5512,D_5508,C_5511),k1_zfmisc_1(u1_struct_0(A_5512))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_73570])).

tff(c_73584,plain,(
    ! [A_5512,D_5508,C_5511] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)))
      | ~ m2_orders_2(D_5508,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_5512),k3_orders_2(A_5512,D_5508,C_5511)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_5508,k1_zfmisc_1(u1_struct_0(A_5512)))
      | ~ m1_subset_1(C_5511,u1_struct_0(A_5512))
      | ~ l1_orders_2(A_5512)
      | ~ v5_orders_2(A_5512)
      | ~ v4_orders_2(A_5512)
      | ~ v3_orders_2(A_5512)
      | v2_struct_0(A_5512)
      | k3_orders_2(A_5512,D_5508,C_5511) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_5512,D_5508,C_5511),k1_zfmisc_1(u1_struct_0(A_5512))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_73578])).

tff(c_76056,plain,(
    ! [A_5626,D_5627,C_5628] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_5626),k3_orders_2(A_5626,D_5627,C_5628)))
      | ~ m2_orders_2(D_5627,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_5626),k3_orders_2(A_5626,D_5627,C_5628)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_5627,k1_zfmisc_1(u1_struct_0(A_5626)))
      | ~ m1_subset_1(C_5628,u1_struct_0(A_5626))
      | ~ l1_orders_2(A_5626)
      | ~ v5_orders_2(A_5626)
      | ~ v4_orders_2(A_5626)
      | ~ v3_orders_2(A_5626)
      | v2_struct_0(A_5626)
      | k3_orders_2(A_5626,D_5627,C_5628) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_5626,D_5627,C_5628),k1_zfmisc_1(u1_struct_0(A_5626))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_73584])).

tff(c_76071,plain,(
    ! [B_4258,C_4259] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4258,C_4259)))
      | ~ m2_orders_2(B_4258,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4259,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4258,C_4259),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_57782,c_76056])).

tff(c_76089,plain,(
    ! [B_4258,C_4259] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4258,C_4259)))
      | ~ m2_orders_2(B_4258,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4259,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4258,C_4259),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_76071])).

tff(c_76096,plain,(
    ! [B_5629,C_5630] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5629,C_5630)))
      | ~ m2_orders_2(B_5629,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_5630,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5629,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5629,C_5630) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5629,C_5630),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76089])).

tff(c_76098,plain,(
    ! [B_5629,C_5630] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5629,C_5630)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5629,C_5630)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_5629,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_5630,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5629,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5629,C_5630) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5629,C_5630),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_76096,c_22])).

tff(c_76104,plain,(
    ! [B_5629,C_5630] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5629,C_5630)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5629,C_5630)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_5629,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_5630,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5629,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5629,C_5630) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5629,C_5630),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_76098])).

tff(c_76106,plain,(
    ! [B_5631,C_5632] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5631,C_5632)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5631,C_5632)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_5631,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_5632,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5631,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5631,C_5632) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5631,C_5632),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76104])).

tff(c_76121,plain,(
    ! [B_4258,C_4259] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4258,C_4259)))
      | ~ m2_orders_2(B_4258,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4259,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4258,C_4259),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_57782,c_76106])).

tff(c_76138,plain,(
    ! [B_4258,C_4259] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4258,C_4259)))
      | ~ m2_orders_2(B_4258,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4259,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4258,C_4259),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_76121])).

tff(c_76142,plain,(
    ! [B_5633,C_5634] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5633,C_5634)))
      | ~ m2_orders_2(B_5633,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_5634,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5633,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5633,C_5634) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5633,C_5634),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76138])).

tff(c_58013,plain,(
    ! [A_4306,B_4307,C_4308,D_4309] :
      ( r2_orders_2(A_4306,B_4307,C_4308)
      | ~ r2_hidden(B_4307,k3_orders_2(A_4306,D_4309,C_4308))
      | ~ m1_subset_1(D_4309,k1_zfmisc_1(u1_struct_0(A_4306)))
      | ~ m1_subset_1(C_4308,u1_struct_0(A_4306))
      | ~ m1_subset_1(B_4307,u1_struct_0(A_4306))
      | ~ l1_orders_2(A_4306)
      | ~ v5_orders_2(A_4306)
      | ~ v4_orders_2(A_4306)
      | ~ v3_orders_2(A_4306)
      | v2_struct_0(A_4306) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58383,plain,(
    ! [A_4379,A_4380,D_4381,C_4382] :
      ( r2_orders_2(A_4379,'#skF_1'(A_4380,k3_orders_2(A_4379,D_4381,C_4382)),C_4382)
      | ~ m1_subset_1(D_4381,k1_zfmisc_1(u1_struct_0(A_4379)))
      | ~ m1_subset_1(C_4382,u1_struct_0(A_4379))
      | ~ m1_subset_1('#skF_1'(A_4380,k3_orders_2(A_4379,D_4381,C_4382)),u1_struct_0(A_4379))
      | ~ l1_orders_2(A_4379)
      | ~ v5_orders_2(A_4379)
      | ~ v4_orders_2(A_4379)
      | ~ v3_orders_2(A_4379)
      | v2_struct_0(A_4379)
      | k3_orders_2(A_4379,D_4381,C_4382) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4379,D_4381,C_4382),k1_zfmisc_1(A_4380)) ) ),
    inference(resolution,[status(thm)],[c_2,c_58013])).

tff(c_58589,plain,(
    ! [A_4402,D_4403,C_4404] :
      ( r2_orders_2(A_4402,'#skF_1'(u1_struct_0(A_4402),k3_orders_2(A_4402,D_4403,C_4404)),C_4404)
      | ~ m1_subset_1(D_4403,k1_zfmisc_1(u1_struct_0(A_4402)))
      | ~ m1_subset_1(C_4404,u1_struct_0(A_4402))
      | ~ l1_orders_2(A_4402)
      | ~ v5_orders_2(A_4402)
      | ~ v4_orders_2(A_4402)
      | ~ v3_orders_2(A_4402)
      | v2_struct_0(A_4402)
      | k3_orders_2(A_4402,D_4403,C_4404) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4402,D_4403,C_4404),k1_zfmisc_1(u1_struct_0(A_4402))) ) ),
    inference(resolution,[status(thm)],[c_4,c_58383])).

tff(c_12,plain,(
    ! [A_7,B_11,C_13] :
      ( r1_orders_2(A_7,B_11,C_13)
      | ~ r2_orders_2(A_7,B_11,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ m1_subset_1(B_11,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59596,plain,(
    ! [A_4511,D_4512,C_4513] :
      ( r1_orders_2(A_4511,'#skF_1'(u1_struct_0(A_4511),k3_orders_2(A_4511,D_4512,C_4513)),C_4513)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4511),k3_orders_2(A_4511,D_4512,C_4513)),u1_struct_0(A_4511))
      | ~ m1_subset_1(D_4512,k1_zfmisc_1(u1_struct_0(A_4511)))
      | ~ m1_subset_1(C_4513,u1_struct_0(A_4511))
      | ~ l1_orders_2(A_4511)
      | ~ v5_orders_2(A_4511)
      | ~ v4_orders_2(A_4511)
      | ~ v3_orders_2(A_4511)
      | v2_struct_0(A_4511)
      | k3_orders_2(A_4511,D_4512,C_4513) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4511,D_4512,C_4513),k1_zfmisc_1(u1_struct_0(A_4511))) ) ),
    inference(resolution,[status(thm)],[c_58589,c_12])).

tff(c_59685,plain,(
    ! [A_4516,B_4517,C_4518] :
      ( r1_orders_2(A_4516,'#skF_1'(u1_struct_0(A_4516),k3_orders_2(A_4516,B_4517,C_4518)),C_4518)
      | ~ m1_subset_1(C_4518,u1_struct_0(A_4516))
      | ~ m1_subset_1(B_4517,k1_zfmisc_1(u1_struct_0(A_4516)))
      | ~ l1_orders_2(A_4516)
      | ~ v5_orders_2(A_4516)
      | ~ v4_orders_2(A_4516)
      | ~ v3_orders_2(A_4516)
      | v2_struct_0(A_4516)
      | k3_orders_2(A_4516,B_4517,C_4518) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4516,B_4517,C_4518),k1_zfmisc_1(u1_struct_0(A_4516))) ) ),
    inference(resolution,[status(thm)],[c_57782,c_59596])).

tff(c_102,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(A_119,B_120,C_121)
      | ~ r1_orders_2(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_107,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_2',B_120,'#skF_3')
      | ~ r1_orders_2('#skF_2',B_120,'#skF_3')
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_111,plain,(
    ! [B_120] :
      ( r3_orders_2('#skF_2',B_120,'#skF_3')
      | ~ r1_orders_2('#skF_2',B_120,'#skF_3')
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_107])).

tff(c_113,plain,(
    ! [B_122] :
      ( r3_orders_2('#skF_2',B_122,'#skF_3')
      | ~ r1_orders_2('#skF_2',B_122,'#skF_3')
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_111])).

tff(c_122,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_113])).

tff(c_123,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_138,plain,(
    ! [C_127,A_128,B_129] :
      ( m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m2_orders_2(C_127,A_128,B_129)
      | ~ m1_orders_1(B_129,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_140,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_138])).

tff(c_143,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_42,c_140])).

tff(c_144,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_143])).

tff(c_212,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_subset_1(k3_orders_2(A_138,B_139,C_140),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_290,plain,(
    ! [A_151,A_152,B_153,C_154] :
      ( m1_subset_1(A_151,u1_struct_0(A_152))
      | ~ r2_hidden(A_151,k3_orders_2(A_152,B_153,C_154))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_212,c_6])).

tff(c_294,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),u1_struct_0(A_152))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_335,plain,(
    ! [B_165,D_166,A_167,C_168] :
      ( r2_hidden(B_165,D_166)
      | ~ r2_hidden(B_165,k3_orders_2(A_167,D_166,C_168))
      | ~ m1_subset_1(D_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(C_168,u1_struct_0(A_167))
      | ~ m1_subset_1(B_165,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_708,plain,(
    ! [A_264,A_265,D_266,C_267] :
      ( r2_hidden('#skF_1'(A_264,k3_orders_2(A_265,D_266,C_267)),D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_subset_1(C_267,u1_struct_0(A_265))
      | ~ m1_subset_1('#skF_1'(A_264,k3_orders_2(A_265,D_266,C_267)),u1_struct_0(A_265))
      | ~ l1_orders_2(A_265)
      | ~ v5_orders_2(A_265)
      | ~ v4_orders_2(A_265)
      | ~ v3_orders_2(A_265)
      | v2_struct_0(A_265)
      | k3_orders_2(A_265,D_266,C_267) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_265,D_266,C_267),k1_zfmisc_1(A_264)) ) ),
    inference(resolution,[status(thm)],[c_2,c_335])).

tff(c_1379,plain,(
    ! [A_339,A_340,B_341,C_342] :
      ( r2_hidden('#skF_1'(A_339,k3_orders_2(A_340,B_341,C_342)),B_341)
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ l1_orders_2(A_340)
      | ~ v5_orders_2(A_340)
      | ~ v4_orders_2(A_340)
      | ~ v3_orders_2(A_340)
      | v2_struct_0(A_340)
      | k3_orders_2(A_340,B_341,C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_340,B_341,C_342),k1_zfmisc_1(A_339)) ) ),
    inference(resolution,[status(thm)],[c_294,c_708])).

tff(c_147,plain,(
    ! [A_4] :
      ( m1_subset_1(A_4,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_4,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_713,plain,(
    ! [A_264,D_266,C_267] :
      ( r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_266,C_267) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_266,C_267),k1_zfmisc_1(A_264))
      | ~ r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_708])).

tff(c_720,plain,(
    ! [A_264,D_266,C_267] :
      ( r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_266,C_267) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_266,C_267),k1_zfmisc_1(A_264))
      | ~ r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_713])).

tff(c_721,plain,(
    ! [A_264,D_266,C_267] :
      ( r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_266,C_267) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_266,C_267),k1_zfmisc_1(A_264))
      | ~ r2_hidden('#skF_1'(A_264,k3_orders_2('#skF_2',D_266,C_267)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_720])).

tff(c_1382,plain,(
    ! [A_339,C_342] :
      ( r2_hidden('#skF_1'(A_339,k3_orders_2('#skF_2','#skF_5',C_342)),'#skF_5')
      | ~ m1_subset_1(C_342,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_342),k1_zfmisc_1(A_339)) ) ),
    inference(resolution,[status(thm)],[c_1379,c_721])).

tff(c_1404,plain,(
    ! [A_339,C_342] :
      ( r2_hidden('#skF_1'(A_339,k3_orders_2('#skF_2','#skF_5',C_342)),'#skF_5')
      | ~ m1_subset_1(C_342,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_342),k1_zfmisc_1(A_339)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_1382])).

tff(c_1405,plain,(
    ! [A_339,C_342] :
      ( r2_hidden('#skF_1'(A_339,k3_orders_2('#skF_2','#skF_5',C_342)),'#skF_5')
      | ~ m1_subset_1(C_342,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_342),k1_zfmisc_1(A_339)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1404])).

tff(c_969,plain,(
    ! [A_292,D_293,C_294] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_292),k3_orders_2(A_292,D_293,C_294)),D_293)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ m1_subset_1(C_294,u1_struct_0(A_292))
      | ~ l1_orders_2(A_292)
      | ~ v5_orders_2(A_292)
      | ~ v4_orders_2(A_292)
      | ~ v3_orders_2(A_292)
      | v2_struct_0(A_292)
      | k3_orders_2(A_292,D_293,C_294) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_292,D_293,C_294),k1_zfmisc_1(u1_struct_0(A_292))) ) ),
    inference(resolution,[status(thm)],[c_4,c_708])).

tff(c_54814,plain,(
    ! [D_4113,A_4112,C_4109,A_4111,D_4110] :
      ( r3_orders_2(A_4111,k1_funct_1(D_4110,u1_struct_0(A_4111)),'#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)))
      | ~ m2_orders_2(D_4113,A_4111,D_4110)
      | ~ m1_orders_1(D_4110,k1_orders_1(u1_struct_0(A_4111)))
      | ~ m1_subset_1(k1_funct_1(D_4110,u1_struct_0(A_4111)),u1_struct_0(A_4111))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)),u1_struct_0(A_4111))
      | ~ l1_orders_2(A_4111)
      | ~ v5_orders_2(A_4111)
      | ~ v4_orders_2(A_4111)
      | ~ v3_orders_2(A_4111)
      | v2_struct_0(A_4111)
      | ~ m1_subset_1(D_4113,k1_zfmisc_1(u1_struct_0(A_4112)))
      | ~ m1_subset_1(C_4109,u1_struct_0(A_4112))
      | ~ l1_orders_2(A_4112)
      | ~ v5_orders_2(A_4112)
      | ~ v4_orders_2(A_4112)
      | ~ v3_orders_2(A_4112)
      | v2_struct_0(A_4112)
      | k3_orders_2(A_4112,D_4113,C_4109) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4112,D_4113,C_4109),k1_zfmisc_1(u1_struct_0(A_4112))) ) ),
    inference(resolution,[status(thm)],[c_969,c_34])).

tff(c_54822,plain,(
    ! [A_4112,D_4113,C_4109] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)))
      | ~ m2_orders_2(D_4113,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_4113,k1_zfmisc_1(u1_struct_0(A_4112)))
      | ~ m1_subset_1(C_4109,u1_struct_0(A_4112))
      | ~ l1_orders_2(A_4112)
      | ~ v5_orders_2(A_4112)
      | ~ v4_orders_2(A_4112)
      | ~ v3_orders_2(A_4112)
      | v2_struct_0(A_4112)
      | k3_orders_2(A_4112,D_4113,C_4109) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4112,D_4113,C_4109),k1_zfmisc_1(u1_struct_0(A_4112))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_54814])).

tff(c_54828,plain,(
    ! [A_4112,D_4113,C_4109] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)))
      | ~ m2_orders_2(D_4113,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4112),k3_orders_2(A_4112,D_4113,C_4109)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_4113,k1_zfmisc_1(u1_struct_0(A_4112)))
      | ~ m1_subset_1(C_4109,u1_struct_0(A_4112))
      | ~ l1_orders_2(A_4112)
      | ~ v5_orders_2(A_4112)
      | ~ v4_orders_2(A_4112)
      | ~ v3_orders_2(A_4112)
      | v2_struct_0(A_4112)
      | k3_orders_2(A_4112,D_4113,C_4109) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4112,D_4113,C_4109),k1_zfmisc_1(u1_struct_0(A_4112))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_54822])).

tff(c_56758,plain,(
    ! [A_4210,D_4211,C_4212] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_4210),k3_orders_2(A_4210,D_4211,C_4212)))
      | ~ m2_orders_2(D_4211,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4210),k3_orders_2(A_4210,D_4211,C_4212)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_4211,k1_zfmisc_1(u1_struct_0(A_4210)))
      | ~ m1_subset_1(C_4212,u1_struct_0(A_4210))
      | ~ l1_orders_2(A_4210)
      | ~ v5_orders_2(A_4210)
      | ~ v4_orders_2(A_4210)
      | ~ v3_orders_2(A_4210)
      | v2_struct_0(A_4210)
      | k3_orders_2(A_4210,D_4211,C_4212) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4210,D_4211,C_4212),k1_zfmisc_1(u1_struct_0(A_4210))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54828])).

tff(c_56773,plain,(
    ! [B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_294,c_56758])).

tff(c_56791,plain,(
    ! [B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_56773])).

tff(c_56798,plain,(
    ! [B_4213,C_4214] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4213,C_4214)))
      | ~ m2_orders_2(B_4213,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4214,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4213,C_4214) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4213,C_4214),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_56791])).

tff(c_56800,plain,(
    ! [B_4213,C_4214] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4213,C_4214)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4213,C_4214)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4213,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4214,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4213,C_4214) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4213,C_4214),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_56798,c_22])).

tff(c_56806,plain,(
    ! [B_4213,C_4214] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4213,C_4214)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4213,C_4214)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4213,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4214,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4213,C_4214) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4213,C_4214),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_56800])).

tff(c_56808,plain,(
    ! [B_4215,C_4216] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4215,C_4216)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4215,C_4216)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_4215,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4216,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4215,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4215,C_4216) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4215,C_4216),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_56806])).

tff(c_56823,plain,(
    ! [B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_294,c_56808])).

tff(c_56840,plain,(
    ! [B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_56823])).

tff(c_56844,plain,(
    ! [B_4217,C_4218] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4217,C_4218)))
      | ~ m2_orders_2(B_4217,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4218,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4217,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4217,C_4218) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4217,C_4218),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_56840])).

tff(c_445,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_orders_2(A_185,B_186,C_187)
      | ~ r2_hidden(B_186,k3_orders_2(A_185,D_188,C_187))
      | ~ m1_subset_1(D_188,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ v5_orders_2(A_185)
      | ~ v4_orders_2(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_914,plain,(
    ! [A_280,A_281,D_282,C_283] :
      ( r2_orders_2(A_280,'#skF_1'(A_281,k3_orders_2(A_280,D_282,C_283)),C_283)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_subset_1(C_283,u1_struct_0(A_280))
      | ~ m1_subset_1('#skF_1'(A_281,k3_orders_2(A_280,D_282,C_283)),u1_struct_0(A_280))
      | ~ l1_orders_2(A_280)
      | ~ v5_orders_2(A_280)
      | ~ v4_orders_2(A_280)
      | ~ v3_orders_2(A_280)
      | v2_struct_0(A_280)
      | k3_orders_2(A_280,D_282,C_283) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_280,D_282,C_283),k1_zfmisc_1(A_281)) ) ),
    inference(resolution,[status(thm)],[c_2,c_445])).

tff(c_919,plain,(
    ! [A_281,D_282,C_283] :
      ( r2_orders_2('#skF_2','#skF_1'(A_281,k3_orders_2('#skF_2',D_282,C_283)),C_283)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_282,C_283) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_282,C_283),k1_zfmisc_1(A_281))
      | ~ r2_hidden('#skF_1'(A_281,k3_orders_2('#skF_2',D_282,C_283)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_914])).

tff(c_926,plain,(
    ! [A_281,D_282,C_283] :
      ( r2_orders_2('#skF_2','#skF_1'(A_281,k3_orders_2('#skF_2',D_282,C_283)),C_283)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_282,C_283) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_282,C_283),k1_zfmisc_1(A_281))
      | ~ r2_hidden('#skF_1'(A_281,k3_orders_2('#skF_2',D_282,C_283)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_919])).

tff(c_1354,plain,(
    ! [A_336,D_337,C_338] :
      ( r2_orders_2('#skF_2','#skF_1'(A_336,k3_orders_2('#skF_2',D_337,C_338)),C_338)
      | ~ m1_subset_1(D_337,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_338,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_337,C_338) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_337,C_338),k1_zfmisc_1(A_336))
      | ~ r2_hidden('#skF_1'(A_336,k3_orders_2('#skF_2',D_337,C_338)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_926])).

tff(c_1366,plain,(
    ! [A_336,D_337,C_338] :
      ( r1_orders_2('#skF_2','#skF_1'(A_336,k3_orders_2('#skF_2',D_337,C_338)),C_338)
      | ~ m1_subset_1('#skF_1'(A_336,k3_orders_2('#skF_2',D_337,C_338)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1(D_337,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_338,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_337,C_338) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_337,C_338),k1_zfmisc_1(A_336))
      | ~ r2_hidden('#skF_1'(A_336,k3_orders_2('#skF_2',D_337,C_338)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1354,c_12])).

tff(c_37283,plain,(
    ! [A_2896,D_2897,C_2898] :
      ( r1_orders_2('#skF_2','#skF_1'(A_2896,k3_orders_2('#skF_2',D_2897,C_2898)),C_2898)
      | ~ m1_subset_1('#skF_1'(A_2896,k3_orders_2('#skF_2',D_2897,C_2898)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_2897,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_2898,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_2897,C_2898) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_2897,C_2898),k1_zfmisc_1(A_2896))
      | ~ r2_hidden('#skF_1'(A_2896,k3_orders_2('#skF_2',D_2897,C_2898)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1366])).

tff(c_37286,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)),C_154)
      | ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)),'#skF_5')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_294,c_37283])).

tff(c_37295,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)),C_154)
      | ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)),'#skF_5')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_37286])).

tff(c_37299,plain,(
    ! [A_2899,B_2900,C_2901] :
      ( r1_orders_2('#skF_2','#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,C_2901)),C_2901)
      | ~ r2_hidden('#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,C_2901)),'#skF_5')
      | ~ m1_subset_1(C_2901,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_2900,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_2900,C_2901) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_2900,C_2901),k1_zfmisc_1(A_2899)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_37295])).

tff(c_148,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_8,plain,(
    ! [A_7,B_11,C_13] :
      ( r2_orders_2(A_7,B_11,C_13)
      | C_13 = B_11
      | ~ r1_orders_2(A_7,B_11,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ m1_subset_1(B_11,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [B_11,A_130] :
      ( r2_orders_2('#skF_2',B_11,A_130)
      | B_11 = A_130
      | ~ r1_orders_2('#skF_2',B_11,A_130)
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_216,plain,(
    ! [B_141,A_142] :
      ( r2_orders_2('#skF_2',B_141,A_142)
      | B_141 = A_142
      | ~ r1_orders_2('#skF_2',B_141,A_142)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_142,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_158])).

tff(c_226,plain,(
    ! [A_142] :
      ( r2_orders_2('#skF_2','#skF_3',A_142)
      | A_142 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_142)
      | ~ r2_hidden(A_142,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_216])).

tff(c_309,plain,(
    ! [A_161,C_162,D_163,B_164] :
      ( ~ r2_orders_2(A_161,C_162,D_163)
      | ~ r1_orders_2(A_161,B_164,C_162)
      | r2_orders_2(A_161,B_164,D_163)
      | ~ m1_subset_1(D_163,u1_struct_0(A_161))
      | ~ m1_subset_1(C_162,u1_struct_0(A_161))
      | ~ m1_subset_1(B_164,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | ~ v5_orders_2(A_161)
      | ~ v4_orders_2(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_315,plain,(
    ! [B_164,A_142] :
      ( ~ r1_orders_2('#skF_2',B_164,'#skF_3')
      | r2_orders_2('#skF_2',B_164,A_142)
      | ~ m1_subset_1(A_142,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_142 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_142)
      | ~ r2_hidden(A_142,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_226,c_309])).

tff(c_341,plain,(
    ! [B_171,A_172] :
      ( ~ r1_orders_2('#skF_2',B_171,'#skF_3')
      | r2_orders_2('#skF_2',B_171,A_172)
      | ~ m1_subset_1(A_172,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_171,u1_struct_0('#skF_2'))
      | A_172 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_172)
      | ~ r2_hidden(A_172,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_315])).

tff(c_356,plain,(
    ! [B_173,A_174] :
      ( ~ r1_orders_2('#skF_2',B_173,'#skF_3')
      | r2_orders_2('#skF_2',B_173,A_174)
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_2'))
      | A_174 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_174)
      | ~ r2_hidden(A_174,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_341])).

tff(c_378,plain,(
    ! [A_177,A_178] :
      ( ~ r1_orders_2('#skF_2',A_177,'#skF_3')
      | r2_orders_2('#skF_2',A_177,A_178)
      | A_178 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_178)
      | ~ r2_hidden(A_178,'#skF_5')
      | ~ r2_hidden(A_177,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_356])).

tff(c_385,plain,(
    ! [A_178] :
      ( ~ m1_subset_1(A_178,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r1_orders_2('#skF_2',A_178,'#skF_3')
      | A_178 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_178)
      | ~ r2_hidden(A_178,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_378,c_10])).

tff(c_395,plain,(
    ! [A_179] :
      ( ~ m1_subset_1(A_179,u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2',A_179,'#skF_3')
      | A_179 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_179)
      | ~ r2_hidden(A_179,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_385])).

tff(c_411,plain,(
    ! [A_4] :
      ( ~ r1_orders_2('#skF_2',A_4,'#skF_3')
      | A_4 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_4)
      | ~ r2_hidden(A_4,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_395])).

tff(c_37336,plain,(
    ! [A_2899,B_2900] :
      ( '#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')))
      | ~ r2_hidden('#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')),'#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_2900,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_2900,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_2900,'#skF_3'),k1_zfmisc_1(A_2899)) ) ),
    inference(resolution,[status(thm)],[c_37299,c_411])).

tff(c_37366,plain,(
    ! [A_2899,B_2900] :
      ( '#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')))
      | ~ r2_hidden('#skF_1'(A_2899,k3_orders_2('#skF_2',B_2900,'#skF_3')),'#skF_5')
      | ~ m1_subset_1(B_2900,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_2900,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_2900,'#skF_3'),k1_zfmisc_1(A_2899)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_37336])).

tff(c_56864,plain,(
    ! [B_4217] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4217,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4217,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_4217,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4217,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4217,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4217,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_56844,c_37366])).

tff(c_56945,plain,(
    ! [B_4219] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4219,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4219,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_4219,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_4219,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4219,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4219,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56864])).

tff(c_56953,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1405,c_56945])).

tff(c_56963,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_144,c_40,c_56953])).

tff(c_56964,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_56963])).

tff(c_56969,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_56964])).

tff(c_56972,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_56969])).

tff(c_56975,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_56972])).

tff(c_56977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_56975])).

tff(c_56979,plain,(
    m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56964])).

tff(c_516,plain,(
    ! [A_213,D_214,B_215,E_216] :
      ( r3_orders_2(A_213,k1_funct_1(D_214,u1_struct_0(A_213)),B_215)
      | ~ r2_hidden(B_215,E_216)
      | ~ m2_orders_2(E_216,A_213,D_214)
      | ~ m1_orders_1(D_214,k1_orders_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(k1_funct_1(D_214,u1_struct_0(A_213)),u1_struct_0(A_213))
      | ~ m1_subset_1(B_215,u1_struct_0(A_213))
      | ~ l1_orders_2(A_213)
      | ~ v5_orders_2(A_213)
      | ~ v4_orders_2(A_213)
      | ~ v3_orders_2(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_661,plain,(
    ! [A_255,D_256,A_257,B_258] :
      ( r3_orders_2(A_255,k1_funct_1(D_256,u1_struct_0(A_255)),'#skF_1'(A_257,B_258))
      | ~ m2_orders_2(B_258,A_255,D_256)
      | ~ m1_orders_1(D_256,k1_orders_1(u1_struct_0(A_255)))
      | ~ m1_subset_1(k1_funct_1(D_256,u1_struct_0(A_255)),u1_struct_0(A_255))
      | ~ m1_subset_1('#skF_1'(A_257,B_258),u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | ~ v5_orders_2(A_255)
      | ~ v4_orders_2(A_255)
      | ~ v3_orders_2(A_255)
      | v2_struct_0(A_255)
      | k1_xboole_0 = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_257)) ) ),
    inference(resolution,[status(thm)],[c_2,c_516])).

tff(c_666,plain,(
    ! [A_257,B_258] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_257,B_258))
      | ~ m2_orders_2(B_258,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_257,B_258),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_661])).

tff(c_669,plain,(
    ! [A_257,B_258] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_257,B_258))
      | ~ m2_orders_2(B_258,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_257,B_258),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_257)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_666])).

tff(c_671,plain,(
    ! [A_259,B_260] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_259,B_260))
      | ~ m2_orders_2(B_260,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_259,B_260),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_260
      | ~ m1_subset_1(B_260,k1_zfmisc_1(A_259)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_669])).

tff(c_701,plain,(
    ! [A_262,B_263] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_262,B_263))
      | ~ m2_orders_2(B_263,'#skF_2','#skF_4')
      | k1_xboole_0 = B_263
      | ~ m1_subset_1(B_263,k1_zfmisc_1(A_262))
      | ~ r2_hidden('#skF_1'(A_262,B_263),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_671])).

tff(c_703,plain,(
    ! [A_262,B_263] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_262,B_263))
      | ~ m1_subset_1('#skF_1'(A_262,B_263),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_263,'#skF_2','#skF_4')
      | k1_xboole_0 = B_263
      | ~ m1_subset_1(B_263,k1_zfmisc_1(A_262))
      | ~ r2_hidden('#skF_1'(A_262,B_263),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_701,c_22])).

tff(c_706,plain,(
    ! [A_262,B_263] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_262,B_263))
      | ~ m1_subset_1('#skF_1'(A_262,B_263),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_263,'#skF_2','#skF_4')
      | k1_xboole_0 = B_263
      | ~ m1_subset_1(B_263,k1_zfmisc_1(A_262))
      | ~ r2_hidden('#skF_1'(A_262,B_263),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_703])).

tff(c_772,plain,(
    ! [A_270,B_271] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_270,B_271))
      | ~ m1_subset_1('#skF_1'(A_270,B_271),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_271,'#skF_2','#skF_4')
      | k1_xboole_0 = B_271
      | ~ m1_subset_1(B_271,k1_zfmisc_1(A_270))
      | ~ r2_hidden('#skF_1'(A_270,B_271),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_706])).

tff(c_795,plain,(
    ! [A_272,B_273] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_272,B_273))
      | ~ m2_orders_2(B_273,'#skF_2','#skF_4')
      | k1_xboole_0 = B_273
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272))
      | ~ r2_hidden('#skF_1'(A_272,B_273),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_772])).

tff(c_164,plain,(
    ! [A_130] :
      ( r2_orders_2('#skF_2',A_130,'#skF_3')
      | A_130 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_130,'#skF_3')
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_148,c_83])).

tff(c_317,plain,(
    ! [B_164,A_130] :
      ( ~ r1_orders_2('#skF_2',B_164,A_130)
      | r2_orders_2('#skF_2',B_164,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_130,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_130 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_130,'#skF_3')
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_164,c_309])).

tff(c_331,plain,(
    ! [B_164,A_130] :
      ( ~ r1_orders_2('#skF_2',B_164,A_130)
      | r2_orders_2('#skF_2',B_164,'#skF_3')
      | ~ m1_subset_1(A_130,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | A_130 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_130,'#skF_3')
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_317])).

tff(c_804,plain,(
    ! [A_272,B_273] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_272,B_273),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | '#skF_1'(A_272,B_273) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_272,B_273),'#skF_3')
      | ~ m2_orders_2(B_273,'#skF_2','#skF_4')
      | k1_xboole_0 = B_273
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272))
      | ~ r2_hidden('#skF_1'(A_272,B_273),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_795,c_331])).

tff(c_818,plain,(
    ! [A_272,B_273] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_272,B_273),u1_struct_0('#skF_2'))
      | '#skF_1'(A_272,B_273) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_272,B_273),'#skF_3')
      | ~ m2_orders_2(B_273,'#skF_2','#skF_4')
      | k1_xboole_0 = B_273
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272))
      | ~ r2_hidden('#skF_1'(A_272,B_273),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_804])).

tff(c_1018,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_818])).

tff(c_1022,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1018,c_12])).

tff(c_1030,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1022])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1030])).

tff(c_1034,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_818])).

tff(c_1225,plain,(
    ! [A_321,D_322,A_323,B_324] :
      ( r1_orders_2(A_321,k1_funct_1(D_322,u1_struct_0(A_321)),'#skF_1'(A_323,B_324))
      | ~ m2_orders_2(B_324,A_321,D_322)
      | ~ m1_orders_1(D_322,k1_orders_1(u1_struct_0(A_321)))
      | ~ m1_subset_1(k1_funct_1(D_322,u1_struct_0(A_321)),u1_struct_0(A_321))
      | ~ m1_subset_1('#skF_1'(A_323,B_324),u1_struct_0(A_321))
      | ~ l1_orders_2(A_321)
      | ~ v5_orders_2(A_321)
      | ~ v4_orders_2(A_321)
      | ~ v3_orders_2(A_321)
      | v2_struct_0(A_321)
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_323)) ) ),
    inference(resolution,[status(thm)],[c_661,c_22])).

tff(c_84,plain,(
    ! [B_114] :
      ( r2_orders_2('#skF_2',B_114,'#skF_3')
      | B_114 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_114,'#skF_3')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_92,plain,(
    ! [B_2] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_319,plain,(
    ! [B_164,B_2] :
      ( ~ r1_orders_2('#skF_2',B_164,'#skF_1'(u1_struct_0('#skF_2'),B_2))
      | r2_orders_2('#skF_2',B_164,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_92,c_309])).

tff(c_334,plain,(
    ! [B_164,B_2] :
      ( ~ r1_orders_2('#skF_2',B_164,'#skF_1'(u1_struct_0('#skF_2'),B_2))
      | r2_orders_2('#skF_2',B_164,'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_164,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_319])).

tff(c_1228,plain,(
    ! [D_322,B_324] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_322,u1_struct_0('#skF_2')),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_324) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_324),'#skF_3')
      | ~ m2_orders_2(B_324,'#skF_2',D_322)
      | ~ m1_orders_1(D_322,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_322,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_324),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1225,c_334])).

tff(c_1245,plain,(
    ! [D_322,B_324] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_322,u1_struct_0('#skF_2')),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_324) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_324),'#skF_3')
      | ~ m2_orders_2(B_324,'#skF_2',D_322)
      | ~ m1_orders_1(D_322,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_322,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_324),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1228])).

tff(c_39066,plain,(
    ! [D_3008,B_3009] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_3008,u1_struct_0('#skF_2')),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_3009) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_3009),'#skF_3')
      | ~ m2_orders_2(B_3009,'#skF_2',D_3008)
      | ~ m1_orders_1(D_3008,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_3008,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_3009),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_3009
      | ~ m1_subset_1(B_3009,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1245])).

tff(c_39068,plain,
    ( r2_orders_2('#skF_2',k1_funct_1('#skF_4',u1_struct_0('#skF_2')),'#skF_3')
    | '#skF_1'(u1_struct_0('#skF_2'),'#skF_5') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),'#skF_3')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_39066])).

tff(c_39071,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | '#skF_1'(u1_struct_0('#skF_2'),'#skF_5') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_44,c_38,c_42,c_38,c_39068])).

tff(c_39072,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),'#skF_5') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_39071])).

tff(c_39073,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_39072])).

tff(c_39079,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_39073])).

tff(c_39083,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_39079])).

tff(c_39173,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_36])).

tff(c_717,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( r2_hidden('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),B_153)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_294,c_708])).

tff(c_39130,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( r2_hidden('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),B_153)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_717])).

tff(c_39158,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),u1_struct_0(A_152))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_294])).

tff(c_1406,plain,(
    ! [C_342,B_341,A_339,A_340,D_82,A_54] :
      ( r3_orders_2(A_54,k1_funct_1(D_82,u1_struct_0(A_54)),'#skF_1'(A_339,k3_orders_2(A_340,B_341,C_342)))
      | ~ m2_orders_2(B_341,A_54,D_82)
      | ~ m1_orders_1(D_82,k1_orders_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(k1_funct_1(D_82,u1_struct_0(A_54)),u1_struct_0(A_54))
      | ~ m1_subset_1('#skF_1'(A_339,k3_orders_2(A_340,B_341,C_342)),u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54)
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ l1_orders_2(A_340)
      | ~ v5_orders_2(A_340)
      | ~ v4_orders_2(A_340)
      | ~ v3_orders_2(A_340)
      | v2_struct_0(A_340)
      | k3_orders_2(A_340,B_341,C_342) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_340,B_341,C_342),k1_zfmisc_1(A_339)) ) ),
    inference(resolution,[status(thm)],[c_1379,c_34])).

tff(c_43069,plain,(
    ! [B_3371,D_3372,A_3376,C_3375,A_3373,A_3374] :
      ( r3_orders_2(A_3373,k1_funct_1(D_3372,u1_struct_0(A_3373)),'#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)))
      | ~ m2_orders_2(B_3371,A_3373,D_3372)
      | ~ m1_orders_1(D_3372,k1_orders_1(u1_struct_0(A_3373)))
      | ~ m1_subset_1(k1_funct_1(D_3372,u1_struct_0(A_3373)),u1_struct_0(A_3373))
      | ~ m1_subset_1('#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)),u1_struct_0(A_3373))
      | ~ l1_orders_2(A_3373)
      | ~ v5_orders_2(A_3373)
      | ~ v4_orders_2(A_3373)
      | ~ v3_orders_2(A_3373)
      | v2_struct_0(A_3373)
      | ~ m1_subset_1(C_3375,u1_struct_0(A_3374))
      | ~ m1_subset_1(B_3371,k1_zfmisc_1(u1_struct_0(A_3374)))
      | ~ l1_orders_2(A_3374)
      | ~ v5_orders_2(A_3374)
      | ~ v4_orders_2(A_3374)
      | ~ v3_orders_2(A_3374)
      | v2_struct_0(A_3374)
      | k3_orders_2(A_3374,B_3371,C_3375) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3374,B_3371,C_3375),k1_zfmisc_1(A_3376)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_1406])).

tff(c_43077,plain,(
    ! [A_3376,A_3374,B_3371,C_3375] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)))
      | ~ m2_orders_2(B_3371,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_3375,u1_struct_0(A_3374))
      | ~ m1_subset_1(B_3371,k1_zfmisc_1(u1_struct_0(A_3374)))
      | ~ l1_orders_2(A_3374)
      | ~ v5_orders_2(A_3374)
      | ~ v4_orders_2(A_3374)
      | ~ v3_orders_2(A_3374)
      | v2_struct_0(A_3374)
      | k3_orders_2(A_3374,B_3371,C_3375) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3374,B_3371,C_3375),k1_zfmisc_1(A_3376)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_43069])).

tff(c_43083,plain,(
    ! [A_3376,A_3374,B_3371,C_3375] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)))
      | ~ m2_orders_2(B_3371,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_3376,k3_orders_2(A_3374,B_3371,C_3375)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_3375,u1_struct_0(A_3374))
      | ~ m1_subset_1(B_3371,k1_zfmisc_1(u1_struct_0(A_3374)))
      | ~ l1_orders_2(A_3374)
      | ~ v5_orders_2(A_3374)
      | ~ v4_orders_2(A_3374)
      | ~ v3_orders_2(A_3374)
      | v2_struct_0(A_3374)
      | k3_orders_2(A_3374,B_3371,C_3375) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3374,B_3371,C_3375),k1_zfmisc_1(A_3376)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_43077])).

tff(c_43675,plain,(
    ! [A_3439,A_3440,B_3441,C_3442] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3439,k3_orders_2(A_3440,B_3441,C_3442)))
      | ~ m2_orders_2(B_3441,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_3439,k3_orders_2(A_3440,B_3441,C_3442)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_3442,u1_struct_0(A_3440))
      | ~ m1_subset_1(B_3441,k1_zfmisc_1(u1_struct_0(A_3440)))
      | ~ l1_orders_2(A_3440)
      | ~ v5_orders_2(A_3440)
      | ~ v4_orders_2(A_3440)
      | ~ v3_orders_2(A_3440)
      | v2_struct_0(A_3440)
      | k3_orders_2(A_3440,B_3441,C_3442) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3440,B_3441,C_3442),k1_zfmisc_1(A_3439)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43083])).

tff(c_43687,plain,(
    ! [A_1,B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_39158,c_43675])).

tff(c_43705,plain,(
    ! [A_1,B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_43687])).

tff(c_43712,plain,(
    ! [A_3443,B_3444,C_3445] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3443,k3_orders_2('#skF_2',B_3444,C_3445)))
      | ~ m2_orders_2(B_3444,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_3445,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3444,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3444,C_3445) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3444,C_3445),k1_zfmisc_1(A_3443)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43705])).

tff(c_43714,plain,(
    ! [A_3443,B_3444,C_3445] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3443,k3_orders_2('#skF_2',B_3444,C_3445)))
      | ~ m1_subset_1('#skF_1'(A_3443,k3_orders_2('#skF_2',B_3444,C_3445)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_3444,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_3445,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3444,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3444,C_3445) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3444,C_3445),k1_zfmisc_1(A_3443)) ) ),
    inference(resolution,[status(thm)],[c_43712,c_22])).

tff(c_43720,plain,(
    ! [A_3443,B_3444,C_3445] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3443,k3_orders_2('#skF_2',B_3444,C_3445)))
      | ~ m1_subset_1('#skF_1'(A_3443,k3_orders_2('#skF_2',B_3444,C_3445)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_3444,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_3445,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3444,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3444,C_3445) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3444,C_3445),k1_zfmisc_1(A_3443)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_43714])).

tff(c_43722,plain,(
    ! [A_3446,B_3447,C_3448] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3446,k3_orders_2('#skF_2',B_3447,C_3448)))
      | ~ m1_subset_1('#skF_1'(A_3446,k3_orders_2('#skF_2',B_3447,C_3448)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_3447,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_3448,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3447,C_3448) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3447,C_3448),k1_zfmisc_1(A_3446)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43720])).

tff(c_43734,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_39158,c_43722])).

tff(c_43755,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_43734])).

tff(c_43759,plain,(
    ! [A_3449,B_3450,C_3451] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3449,k3_orders_2('#skF_2',B_3450,C_3451)))
      | ~ m2_orders_2(B_3450,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_3451,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3450,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3450,C_3451) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3450,C_3451),k1_zfmisc_1(A_3449)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43755])).

tff(c_1450,plain,(
    ! [A_349,A_350,B_351,C_352] :
      ( r2_orders_2(A_349,'#skF_1'(A_350,k3_orders_2(A_349,B_351,C_352)),C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_349))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_orders_2(A_349)
      | ~ v5_orders_2(A_349)
      | ~ v4_orders_2(A_349)
      | ~ v3_orders_2(A_349)
      | v2_struct_0(A_349)
      | k3_orders_2(A_349,B_351,C_352) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_349,B_351,C_352),k1_zfmisc_1(A_350)) ) ),
    inference(resolution,[status(thm)],[c_294,c_914])).

tff(c_1472,plain,(
    ! [A_349,A_350,B_351,C_352] :
      ( r1_orders_2(A_349,'#skF_1'(A_350,k3_orders_2(A_349,B_351,C_352)),C_352)
      | ~ m1_subset_1('#skF_1'(A_350,k3_orders_2(A_349,B_351,C_352)),u1_struct_0(A_349))
      | ~ m1_subset_1(C_352,u1_struct_0(A_349))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_orders_2(A_349)
      | ~ v5_orders_2(A_349)
      | ~ v4_orders_2(A_349)
      | ~ v3_orders_2(A_349)
      | v2_struct_0(A_349)
      | k3_orders_2(A_349,B_351,C_352) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_349,B_351,C_352),k1_zfmisc_1(A_350)) ) ),
    inference(resolution,[status(thm)],[c_1450,c_12])).

tff(c_40014,plain,(
    ! [A_3119,A_3120,B_3121,C_3122] :
      ( r1_orders_2(A_3119,'#skF_1'(A_3120,k3_orders_2(A_3119,B_3121,C_3122)),C_3122)
      | ~ m1_subset_1('#skF_1'(A_3120,k3_orders_2(A_3119,B_3121,C_3122)),u1_struct_0(A_3119))
      | ~ m1_subset_1(C_3122,u1_struct_0(A_3119))
      | ~ m1_subset_1(B_3121,k1_zfmisc_1(u1_struct_0(A_3119)))
      | ~ l1_orders_2(A_3119)
      | ~ v5_orders_2(A_3119)
      | ~ v4_orders_2(A_3119)
      | ~ v3_orders_2(A_3119)
      | v2_struct_0(A_3119)
      | k3_orders_2(A_3119,B_3121,C_3122) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3119,B_3121,C_3122),k1_zfmisc_1(A_3120)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_1472])).

tff(c_40025,plain,(
    ! [A_3120,B_3121,C_3122] :
      ( r1_orders_2('#skF_2','#skF_1'(A_3120,k3_orders_2('#skF_2',B_3121,C_3122)),C_3122)
      | ~ m1_subset_1(C_3122,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3121,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_3121,C_3122) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3121,C_3122),k1_zfmisc_1(A_3120))
      | ~ r2_hidden('#skF_1'(A_3120,k3_orders_2('#skF_2',B_3121,C_3122)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_40014])).

tff(c_40033,plain,(
    ! [A_3120,B_3121,C_3122] :
      ( r1_orders_2('#skF_2','#skF_1'(A_3120,k3_orders_2('#skF_2',B_3121,C_3122)),C_3122)
      | ~ m1_subset_1(C_3122,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3121,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_3121,C_3122) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3121,C_3122),k1_zfmisc_1(A_3120))
      | ~ r2_hidden('#skF_1'(A_3120,k3_orders_2('#skF_2',B_3121,C_3122)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_40025])).

tff(c_40052,plain,(
    ! [A_3126,B_3127,C_3128] :
      ( r1_orders_2('#skF_2','#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,C_3128)),C_3128)
      | ~ m1_subset_1(C_3128,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3127,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3127,C_3128) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3127,C_3128),k1_zfmisc_1(A_3126))
      | ~ r2_hidden('#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,C_3128)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40033])).

tff(c_40073,plain,(
    ! [A_3126,B_3127] :
      ( '#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3127,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3127,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3127,'#skF_3'),k1_zfmisc_1(A_3126))
      | ~ r2_hidden('#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40052,c_411])).

tff(c_40098,plain,(
    ! [A_3126,B_3127] :
      ( '#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')))
      | ~ m1_subset_1(B_3127,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3127,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3127,'#skF_3'),k1_zfmisc_1(A_3126))
      | ~ r2_hidden('#skF_1'(A_3126,k3_orders_2('#skF_2',B_3127,'#skF_3')),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40073])).

tff(c_43781,plain,(
    ! [A_3449,B_3450] :
      ( '#skF_1'(A_3449,k3_orders_2('#skF_2',B_3450,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_3449,k3_orders_2('#skF_2',B_3450,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_3450,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3450,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3450,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3450,'#skF_3'),k1_zfmisc_1(A_3449)) ) ),
    inference(resolution,[status(thm)],[c_43759,c_40098])).

tff(c_43858,plain,(
    ! [A_3452,B_3453] :
      ( '#skF_1'(A_3452,k3_orders_2('#skF_2',B_3453,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_3452,k3_orders_2('#skF_2',B_3453,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_3453,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_3453,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3453,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3453,'#skF_3'),k1_zfmisc_1(A_3452)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_43781])).

tff(c_43862,plain,(
    ! [A_1] :
      ( '#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_39130,c_43858])).

tff(c_43873,plain,(
    ! [A_1] :
      ( '#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_40,c_43862])).

tff(c_43954,plain,(
    ! [A_3460] :
      ( '#skF_1'(A_3460,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_3460)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_39173,c_54,c_43873])).

tff(c_43958,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_43954])).

tff(c_43961,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_43958])).

tff(c_43962,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43961])).

tff(c_43756,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43755])).

tff(c_43969,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43962,c_43756])).

tff(c_44180,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_44,c_40,c_43969])).

tff(c_44181,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_39173,c_123,c_44180])).

tff(c_44359,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_44181])).

tff(c_44362,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_44359])).

tff(c_44364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_44362])).

tff(c_44366,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39072])).

tff(c_1242,plain,(
    ! [A_323,B_324] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_323,B_324))
      | ~ m2_orders_2(B_324,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_323,B_324),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_323)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1225])).

tff(c_1261,plain,(
    ! [A_323,B_324] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_323,B_324))
      | ~ m2_orders_2(B_324,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_323,B_324),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_1242])).

tff(c_1262,plain,(
    ! [A_323,B_324] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_323,B_324))
      | ~ m2_orders_2(B_324,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_323,B_324),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_324
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_323)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1261])).

tff(c_44423,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'))
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44366,c_1262])).

tff(c_44448,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_40,c_44423])).

tff(c_44464,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44448])).

tff(c_44555,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_36])).

tff(c_44512,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( r2_hidden('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),B_153)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_717])).

tff(c_44540,plain,(
    ! [A_1,A_152,B_153,C_154] :
      ( m1_subset_1('#skF_1'(A_1,k3_orders_2(A_152,B_153,C_154)),u1_struct_0(A_152))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152)
      | k3_orders_2(A_152,B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_152,B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_294])).

tff(c_49336,plain,(
    ! [C_3819,A_3818,D_3816,B_3815,A_3820,A_3817] :
      ( r3_orders_2(A_3817,k1_funct_1(D_3816,u1_struct_0(A_3817)),'#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)))
      | ~ m2_orders_2(B_3815,A_3817,D_3816)
      | ~ m1_orders_1(D_3816,k1_orders_1(u1_struct_0(A_3817)))
      | ~ m1_subset_1(k1_funct_1(D_3816,u1_struct_0(A_3817)),u1_struct_0(A_3817))
      | ~ m1_subset_1('#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)),u1_struct_0(A_3817))
      | ~ l1_orders_2(A_3817)
      | ~ v5_orders_2(A_3817)
      | ~ v4_orders_2(A_3817)
      | ~ v3_orders_2(A_3817)
      | v2_struct_0(A_3817)
      | ~ m1_subset_1(C_3819,u1_struct_0(A_3818))
      | ~ m1_subset_1(B_3815,k1_zfmisc_1(u1_struct_0(A_3818)))
      | ~ l1_orders_2(A_3818)
      | ~ v5_orders_2(A_3818)
      | ~ v4_orders_2(A_3818)
      | ~ v3_orders_2(A_3818)
      | v2_struct_0(A_3818)
      | k3_orders_2(A_3818,B_3815,C_3819) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3818,B_3815,C_3819),k1_zfmisc_1(A_3820)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_1406])).

tff(c_49344,plain,(
    ! [A_3820,A_3818,B_3815,C_3819] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)))
      | ~ m2_orders_2(B_3815,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_3819,u1_struct_0(A_3818))
      | ~ m1_subset_1(B_3815,k1_zfmisc_1(u1_struct_0(A_3818)))
      | ~ l1_orders_2(A_3818)
      | ~ v5_orders_2(A_3818)
      | ~ v4_orders_2(A_3818)
      | ~ v3_orders_2(A_3818)
      | v2_struct_0(A_3818)
      | k3_orders_2(A_3818,B_3815,C_3819) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3818,B_3815,C_3819),k1_zfmisc_1(A_3820)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_49336])).

tff(c_49350,plain,(
    ! [A_3820,A_3818,B_3815,C_3819] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)))
      | ~ m2_orders_2(B_3815,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_3820,k3_orders_2(A_3818,B_3815,C_3819)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_3819,u1_struct_0(A_3818))
      | ~ m1_subset_1(B_3815,k1_zfmisc_1(u1_struct_0(A_3818)))
      | ~ l1_orders_2(A_3818)
      | ~ v5_orders_2(A_3818)
      | ~ v4_orders_2(A_3818)
      | ~ v3_orders_2(A_3818)
      | v2_struct_0(A_3818)
      | k3_orders_2(A_3818,B_3815,C_3819) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3818,B_3815,C_3819),k1_zfmisc_1(A_3820)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_49344])).

tff(c_52644,plain,(
    ! [A_4047,A_4048,B_4049,C_4050] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4047,k3_orders_2(A_4048,B_4049,C_4050)))
      | ~ m2_orders_2(B_4049,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_4047,k3_orders_2(A_4048,B_4049,C_4050)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_4050,u1_struct_0(A_4048))
      | ~ m1_subset_1(B_4049,k1_zfmisc_1(u1_struct_0(A_4048)))
      | ~ l1_orders_2(A_4048)
      | ~ v5_orders_2(A_4048)
      | ~ v4_orders_2(A_4048)
      | ~ v3_orders_2(A_4048)
      | v2_struct_0(A_4048)
      | k3_orders_2(A_4048,B_4049,C_4050) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_4048,B_4049,C_4050),k1_zfmisc_1(A_4047)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_49350])).

tff(c_52659,plain,(
    ! [A_1,B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_44540,c_52644])).

tff(c_52684,plain,(
    ! [A_1,B_153,C_154] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_52659])).

tff(c_52692,plain,(
    ! [A_4051,B_4052,C_4053] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_4051,k3_orders_2('#skF_2',B_4052,C_4053)))
      | ~ m2_orders_2(B_4052,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4053,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4052,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4052,C_4053) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4052,C_4053),k1_zfmisc_1(A_4051)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52684])).

tff(c_52694,plain,(
    ! [A_4051,B_4052,C_4053] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4051,k3_orders_2('#skF_2',B_4052,C_4053)))
      | ~ m1_subset_1('#skF_1'(A_4051,k3_orders_2('#skF_2',B_4052,C_4053)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4052,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4053,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4052,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4052,C_4053) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4052,C_4053),k1_zfmisc_1(A_4051)) ) ),
    inference(resolution,[status(thm)],[c_52692,c_22])).

tff(c_52703,plain,(
    ! [A_4051,B_4052,C_4053] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4051,k3_orders_2('#skF_2',B_4052,C_4053)))
      | ~ m1_subset_1('#skF_1'(A_4051,k3_orders_2('#skF_2',B_4052,C_4053)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_4052,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4053,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4052,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4052,C_4053) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4052,C_4053),k1_zfmisc_1(A_4051)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_52694])).

tff(c_52705,plain,(
    ! [A_4054,B_4055,C_4056] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4054,k3_orders_2('#skF_2',B_4055,C_4056)))
      | ~ m1_subset_1('#skF_1'(A_4054,k3_orders_2('#skF_2',B_4055,C_4056)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_4055,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4056,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4055,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4055,C_4056) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4055,C_4056),k1_zfmisc_1(A_4054)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52703])).

tff(c_52720,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_44540,c_52705])).

tff(c_52745,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_52720])).

tff(c_52753,plain,(
    ! [A_4057,B_4058,C_4059] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_4057,k3_orders_2('#skF_2',B_4058,C_4059)))
      | ~ m2_orders_2(B_4058,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_4059,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4058,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4058,C_4059) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4058,C_4059),k1_zfmisc_1(A_4057)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52745])).

tff(c_46205,plain,(
    ! [A_3653,A_3654,B_3655,C_3656] :
      ( m1_subset_1('#skF_1'(A_3653,k3_orders_2(A_3654,B_3655,C_3656)),u1_struct_0(A_3654))
      | ~ m1_subset_1(C_3656,u1_struct_0(A_3654))
      | ~ m1_subset_1(B_3655,k1_zfmisc_1(u1_struct_0(A_3654)))
      | ~ l1_orders_2(A_3654)
      | ~ v5_orders_2(A_3654)
      | ~ v4_orders_2(A_3654)
      | ~ v3_orders_2(A_3654)
      | v2_struct_0(A_3654)
      | k3_orders_2(A_3654,B_3655,C_3656) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3654,B_3655,C_3656),k1_zfmisc_1(A_3653)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_294])).

tff(c_45297,plain,(
    ! [A_349,A_350,B_351,C_352] :
      ( r1_orders_2(A_349,'#skF_1'(A_350,k3_orders_2(A_349,B_351,C_352)),C_352)
      | ~ m1_subset_1('#skF_1'(A_350,k3_orders_2(A_349,B_351,C_352)),u1_struct_0(A_349))
      | ~ m1_subset_1(C_352,u1_struct_0(A_349))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_orders_2(A_349)
      | ~ v5_orders_2(A_349)
      | ~ v4_orders_2(A_349)
      | ~ v3_orders_2(A_349)
      | v2_struct_0(A_349)
      | k3_orders_2(A_349,B_351,C_352) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_349,B_351,C_352),k1_zfmisc_1(A_350)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44464,c_1472])).

tff(c_46455,plain,(
    ! [A_3675,A_3676,B_3677,C_3678] :
      ( r1_orders_2(A_3675,'#skF_1'(A_3676,k3_orders_2(A_3675,B_3677,C_3678)),C_3678)
      | ~ m1_subset_1(C_3678,u1_struct_0(A_3675))
      | ~ m1_subset_1(B_3677,k1_zfmisc_1(u1_struct_0(A_3675)))
      | ~ l1_orders_2(A_3675)
      | ~ v5_orders_2(A_3675)
      | ~ v4_orders_2(A_3675)
      | ~ v3_orders_2(A_3675)
      | v2_struct_0(A_3675)
      | k3_orders_2(A_3675,B_3677,C_3678) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2(A_3675,B_3677,C_3678),k1_zfmisc_1(A_3676)) ) ),
    inference(resolution,[status(thm)],[c_46205,c_45297])).

tff(c_46504,plain,(
    ! [A_3676,B_3677] :
      ( '#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')))
      | ~ r2_hidden('#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')),'#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_3677,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_3677,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3677,'#skF_3'),k1_zfmisc_1(A_3676)) ) ),
    inference(resolution,[status(thm)],[c_46455,c_411])).

tff(c_46565,plain,(
    ! [A_3676,B_3677] :
      ( '#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')))
      | ~ r2_hidden('#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')),'#skF_5')
      | ~ m1_subset_1(B_3677,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_3677,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3677,'#skF_3'),k1_zfmisc_1(A_3676)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_46504])).

tff(c_46566,plain,(
    ! [A_3676,B_3677] :
      ( '#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')))
      | ~ r2_hidden('#skF_1'(A_3676,k3_orders_2('#skF_2',B_3677,'#skF_3')),'#skF_5')
      | ~ m1_subset_1(B_3677,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_3677,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_3677,'#skF_3'),k1_zfmisc_1(A_3676)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_46565])).

tff(c_52783,plain,(
    ! [A_4057,B_4058] :
      ( '#skF_1'(A_4057,k3_orders_2('#skF_2',B_4058,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_4057,k3_orders_2('#skF_2',B_4058,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_4058,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4058,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4058,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4058,'#skF_3'),k1_zfmisc_1(A_4057)) ) ),
    inference(resolution,[status(thm)],[c_52753,c_46566])).

tff(c_52882,plain,(
    ! [A_4060,B_4061] :
      ( '#skF_1'(A_4060,k3_orders_2('#skF_2',B_4061,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_4060,k3_orders_2('#skF_2',B_4061,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_4061,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_4061,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4061,'#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4061,'#skF_3'),k1_zfmisc_1(A_4060)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52783])).

tff(c_52890,plain,(
    ! [A_1] :
      ( '#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_44512,c_52882])).

tff(c_52904,plain,(
    ! [A_1] :
      ( '#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_40,c_52890])).

tff(c_52921,plain,(
    ! [A_4066] :
      ( '#skF_1'(A_4066,k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(A_4066)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44555,c_54,c_52904])).

tff(c_52925,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_52921])).

tff(c_52928,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_52925])).

tff(c_52929,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52928])).

tff(c_52746,plain,(
    ! [A_1,B_153,C_154] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1,k3_orders_2('#skF_2',B_153,C_154)))
      | ~ m2_orders_2(B_153,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_153,C_154) = '#skF_5'
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_153,C_154),k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52745])).

tff(c_52936,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52929,c_52746])).

tff(c_53187,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = '#skF_5'
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_44,c_40,c_52936])).

tff(c_53188,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44555,c_123,c_53187])).

tff(c_53408,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_53188])).

tff(c_53411,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_53408])).

tff(c_53413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_53411])).

tff(c_53415,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44448])).

tff(c_667,plain,(
    ! [A_255,D_256,A_257,B_258] :
      ( r1_orders_2(A_255,k1_funct_1(D_256,u1_struct_0(A_255)),'#skF_1'(A_257,B_258))
      | ~ m2_orders_2(B_258,A_255,D_256)
      | ~ m1_orders_1(D_256,k1_orders_1(u1_struct_0(A_255)))
      | ~ m1_subset_1(k1_funct_1(D_256,u1_struct_0(A_255)),u1_struct_0(A_255))
      | ~ m1_subset_1('#skF_1'(A_257,B_258),u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | ~ v5_orders_2(A_255)
      | ~ v4_orders_2(A_255)
      | ~ v3_orders_2(A_255)
      | v2_struct_0(A_255)
      | k1_xboole_0 = B_258
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_257)) ) ),
    inference(resolution,[status(thm)],[c_661,c_22])).

tff(c_167,plain,(
    ! [B_11,A_130] :
      ( r2_orders_2('#skF_2',B_11,A_130)
      | B_11 = A_130
      | ~ r1_orders_2('#skF_2',B_11,A_130)
      | ~ m1_subset_1(B_11,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_158])).

tff(c_53949,plain,(
    ! [A_4084] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4084)
      | A_4084 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4084)
      | ~ r2_hidden(A_4084,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44366,c_167])).

tff(c_24,plain,(
    ! [A_24,C_36,D_38,B_32] :
      ( ~ r2_orders_2(A_24,C_36,D_38)
      | ~ r1_orders_2(A_24,B_32,C_36)
      | r2_orders_2(A_24,B_32,D_38)
      | ~ m1_subset_1(D_38,u1_struct_0(A_24))
      | ~ m1_subset_1(C_36,u1_struct_0(A_24))
      | ~ m1_subset_1(B_32,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24)
      | ~ v4_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_53973,plain,(
    ! [B_32,A_4084] :
      ( ~ r1_orders_2('#skF_2',B_32,'#skF_1'(u1_struct_0('#skF_2'),'#skF_5'))
      | r2_orders_2('#skF_2',B_32,A_4084)
      | ~ m1_subset_1(A_4084,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_4084 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4084)
      | ~ r2_hidden(A_4084,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_53949,c_24])).

tff(c_55180,plain,(
    ! [B_4130,A_4131] :
      ( ~ r1_orders_2('#skF_2',B_4130,'#skF_1'(u1_struct_0('#skF_2'),'#skF_5'))
      | r2_orders_2('#skF_2',B_4130,A_4131)
      | ~ m1_subset_1(A_4131,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4130,u1_struct_0('#skF_2'))
      | A_4131 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4131)
      | ~ r2_hidden(A_4131,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44366,c_53973])).

tff(c_55210,plain,(
    ! [D_256,A_4131] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_256,u1_struct_0('#skF_2')),A_4131)
      | ~ m1_subset_1(A_4131,u1_struct_0('#skF_2'))
      | A_4131 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4131)
      | ~ r2_hidden(A_4131,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_256)
      | ~ m1_orders_1(D_256,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_256,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_667,c_55180])).

tff(c_55252,plain,(
    ! [D_256,A_4131] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_256,u1_struct_0('#skF_2')),A_4131)
      | ~ m1_subset_1(A_4131,u1_struct_0('#skF_2'))
      | A_4131 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4131)
      | ~ r2_hidden(A_4131,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_256)
      | ~ m1_orders_1(D_256,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_256,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_52,c_50,c_48,c_46,c_44366,c_55210])).

tff(c_55266,plain,(
    ! [D_4132,A_4133] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_4132,u1_struct_0('#skF_2')),A_4133)
      | ~ m1_subset_1(A_4133,u1_struct_0('#skF_2'))
      | A_4133 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4133)
      | ~ r2_hidden(A_4133,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_4132)
      | ~ m1_orders_1(D_4132,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1(D_4132,u1_struct_0('#skF_2')),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_53415,c_54,c_55252])).

tff(c_55323,plain,(
    ! [D_4135,A_4136] :
      ( r2_orders_2('#skF_2',k1_funct_1(D_4135,u1_struct_0('#skF_2')),A_4136)
      | ~ m1_subset_1(A_4136,u1_struct_0('#skF_2'))
      | A_4136 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4136)
      | ~ r2_hidden(A_4136,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_4135)
      | ~ m1_orders_1(D_4135,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(k1_funct_1(D_4135,u1_struct_0('#skF_2')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_147,c_55266])).

tff(c_55342,plain,(
    ! [D_4135,A_4136] :
      ( r1_orders_2('#skF_2',k1_funct_1(D_4135,u1_struct_0('#skF_2')),A_4136)
      | ~ m1_subset_1(k1_funct_1(D_4135,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1(A_4136,u1_struct_0('#skF_2'))
      | A_4136 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4136)
      | ~ r2_hidden(A_4136,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_4135)
      | ~ m1_orders_1(D_4135,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(k1_funct_1(D_4135,u1_struct_0('#skF_2')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_55323,c_12])).

tff(c_56654,plain,(
    ! [D_4206,A_4207] :
      ( r1_orders_2('#skF_2',k1_funct_1(D_4206,u1_struct_0('#skF_2')),A_4207)
      | ~ m1_subset_1(k1_funct_1(D_4206,u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_4207,u1_struct_0('#skF_2'))
      | A_4207 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4207)
      | ~ r2_hidden(A_4207,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2',D_4206)
      | ~ m1_orders_1(D_4206,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(k1_funct_1(D_4206,u1_struct_0('#skF_2')),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55342])).

tff(c_56659,plain,(
    ! [A_4207] :
      ( r1_orders_2('#skF_2',k1_funct_1('#skF_4',u1_struct_0('#skF_2')),A_4207)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_4207,u1_struct_0('#skF_2'))
      | A_4207 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4207)
      | ~ r2_hidden(A_4207,'#skF_5')
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_56654])).

tff(c_56662,plain,(
    ! [A_4207] :
      ( r1_orders_2('#skF_2','#skF_3',A_4207)
      | ~ m1_subset_1(A_4207,u1_struct_0('#skF_2'))
      | A_4207 = '#skF_1'(u1_struct_0('#skF_2'),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),'#skF_5'),A_4207)
      | ~ r2_hidden(A_4207,'#skF_5')
      | ~ r2_hidden('#skF_3','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_40,c_44,c_38,c_56659])).

tff(c_56663,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56662])).

tff(c_56978,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56964])).

tff(c_57114,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_56978,c_717])).

tff(c_57339,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_144,c_44,c_57114])).

tff(c_57340,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_54,c_56663,c_57339])).

tff(c_57530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56979,c_57340])).

tff(c_57532,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56662])).

tff(c_57579,plain,(
    ! [A_4226,D_4227] :
      ( r3_orders_2(A_4226,k1_funct_1(D_4227,u1_struct_0(A_4226)),'#skF_3')
      | ~ m2_orders_2('#skF_5',A_4226,D_4227)
      | ~ m1_orders_1(D_4227,k1_orders_1(u1_struct_0(A_4226)))
      | ~ m1_subset_1(k1_funct_1(D_4227,u1_struct_0(A_4226)),u1_struct_0(A_4226))
      | ~ m1_subset_1('#skF_3',u1_struct_0(A_4226))
      | ~ l1_orders_2(A_4226)
      | ~ v5_orders_2(A_4226)
      | ~ v4_orders_2(A_4226)
      | ~ v3_orders_2(A_4226)
      | v2_struct_0(A_4226) ) ),
    inference(resolution,[status(thm)],[c_57532,c_34])).

tff(c_57586,plain,
    ( r3_orders_2('#skF_2',k1_funct_1('#skF_4',u1_struct_0('#skF_2')),'#skF_3')
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_57579])).

tff(c_57592,plain,
    ( r3_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_44,c_42,c_40,c_38,c_57586])).

tff(c_57593,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_57592])).

tff(c_57595,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_57593,c_22])).

tff(c_57598,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_57595])).

tff(c_57600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_123,c_57598])).

tff(c_57602,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_57995,plain,(
    ! [A_4300,B_4301,B_4302] :
      ( r2_orders_2(A_4300,B_4301,'#skF_1'(u1_struct_0(A_4300),B_4302))
      | B_4301 = '#skF_1'(u1_struct_0(A_4300),B_4302)
      | ~ r1_orders_2(A_4300,B_4301,'#skF_1'(u1_struct_0(A_4300),B_4302))
      | ~ m1_subset_1(B_4301,u1_struct_0(A_4300))
      | ~ l1_orders_2(A_4300)
      | k1_xboole_0 = B_4302
      | ~ m1_subset_1(B_4302,k1_zfmisc_1(u1_struct_0(A_4300))) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_58988,plain,(
    ! [A_4446,B_4447,B_4448,B_4449] :
      ( ~ r1_orders_2(A_4446,B_4447,B_4448)
      | r2_orders_2(A_4446,B_4447,'#skF_1'(u1_struct_0(A_4446),B_4449))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_4446),B_4449),u1_struct_0(A_4446))
      | ~ m1_subset_1(B_4447,u1_struct_0(A_4446))
      | ~ v5_orders_2(A_4446)
      | ~ v4_orders_2(A_4446)
      | B_4448 = '#skF_1'(u1_struct_0(A_4446),B_4449)
      | ~ r1_orders_2(A_4446,B_4448,'#skF_1'(u1_struct_0(A_4446),B_4449))
      | ~ m1_subset_1(B_4448,u1_struct_0(A_4446))
      | ~ l1_orders_2(A_4446)
      | k1_xboole_0 = B_4449
      | ~ m1_subset_1(B_4449,k1_zfmisc_1(u1_struct_0(A_4446))) ) ),
    inference(resolution,[status(thm)],[c_57995,c_24])).

tff(c_59002,plain,(
    ! [B_4449] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4449))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4449),u1_struct_0('#skF_2'))
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | '#skF_1'(u1_struct_0('#skF_2'),B_4449) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4449))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | k1_xboole_0 = B_4449
      | ~ m1_subset_1(B_4449,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_57602,c_58988])).

tff(c_59031,plain,(
    ! [B_4452] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4452))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4452),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4452) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4452))
      | k1_xboole_0 = B_4452
      | ~ m1_subset_1(B_4452,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_50,c_48,c_59002])).

tff(c_59054,plain,(
    ! [B_4453] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4453))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4453) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4453))
      | k1_xboole_0 = B_4453
      | ~ m1_subset_1(B_4453,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_59031])).

tff(c_59056,plain,(
    ! [B_32,B_4453] :
      ( ~ r1_orders_2('#skF_2',B_32,'#skF_3')
      | r2_orders_2('#skF_2',B_32,'#skF_1'(u1_struct_0('#skF_2'),B_4453))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4453),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | '#skF_1'(u1_struct_0('#skF_2'),B_4453) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4453))
      | k1_xboole_0 = B_4453
      | ~ m1_subset_1(B_4453,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_59054,c_24])).

tff(c_59132,plain,(
    ! [B_4469,B_4470] :
      ( ~ r1_orders_2('#skF_2',B_4469,'#skF_3')
      | r2_orders_2('#skF_2',B_4469,'#skF_1'(u1_struct_0('#skF_2'),B_4470))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4470),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4469,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4470) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4470))
      | k1_xboole_0 = B_4470
      | ~ m1_subset_1(B_4470,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_59056])).

tff(c_59152,plain,(
    ! [B_4471,B_4472] :
      ( ~ r1_orders_2('#skF_2',B_4471,'#skF_3')
      | r2_orders_2('#skF_2',B_4471,'#skF_1'(u1_struct_0('#skF_2'),B_4472))
      | ~ m1_subset_1(B_4471,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4472) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4472))
      | k1_xboole_0 = B_4472
      | ~ m1_subset_1(B_4472,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_59132])).

tff(c_59159,plain,(
    ! [B_4472] :
      ( ~ l1_orders_2('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_4472),'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4472),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4472) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4472))
      | k1_xboole_0 = B_4472
      | ~ m1_subset_1(B_4472,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_59152,c_10])).

tff(c_59169,plain,(
    ! [B_4473] :
      ( ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_4473),'#skF_3')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_4473),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_4473) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_4473))
      | k1_xboole_0 = B_4473
      | ~ m1_subset_1(B_4473,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_59159])).

tff(c_59191,plain,(
    ! [B_2] :
      ( ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_2))
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_59169])).

tff(c_59699,plain,(
    ! [B_4517] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_4517,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4517,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4517,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_59685,c_59191])).

tff(c_59747,plain,(
    ! [B_4517] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')))
      | ~ m1_subset_1(B_4517,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_4517,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4517,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_59699])).

tff(c_59748,plain,(
    ! [B_4517] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_4517,'#skF_3')))
      | ~ m1_subset_1(B_4517,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_4517,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_4517,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_59747])).

tff(c_76162,plain,(
    ! [B_5633] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5633,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_5633,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_5633,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5633,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5633,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_76142,c_59748])).

tff(c_76243,plain,(
    ! [B_5635] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5635,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_5635,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_5635,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_5635,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_5635,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76162])).

tff(c_76247,plain,(
    ! [B_15] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_15,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_15,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_15,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_76243])).

tff(c_76250,plain,(
    ! [B_15] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_15,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_15,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_15,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_76247])).

tff(c_76252,plain,(
    ! [B_5636] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_5636,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_5636,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_5636,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_5636,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76250])).

tff(c_76271,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57630,c_76252])).

tff(c_76285,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76271])).

tff(c_76286,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_76285])).

tff(c_58392,plain,(
    ! [A_4257,A_1,B_4258,C_4259] :
      ( r2_orders_2(A_4257,'#skF_1'(A_1,k3_orders_2(A_4257,B_4258,C_4259)),C_4259)
      | ~ m1_subset_1(C_4259,u1_struct_0(A_4257))
      | ~ m1_subset_1(B_4258,k1_zfmisc_1(u1_struct_0(A_4257)))
      | ~ l1_orders_2(A_4257)
      | ~ v5_orders_2(A_4257)
      | ~ v4_orders_2(A_4257)
      | ~ v3_orders_2(A_4257)
      | v2_struct_0(A_4257)
      | k3_orders_2(A_4257,B_4258,C_4259) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_4257,B_4258,C_4259),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_57782,c_58383])).

tff(c_76406,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_76286,c_58392])).

tff(c_76642,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_57630,c_44,c_76406])).

tff(c_76643,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_54,c_58588,c_76642])).

tff(c_76741,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_76643])).

tff(c_76744,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_57630,c_44,c_76741])).

tff(c_76746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_76744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:19:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.39/16.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.64/16.99  
% 26.64/16.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.64/16.99  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 26.64/16.99  
% 26.64/16.99  %Foreground sorts:
% 26.64/16.99  
% 26.64/16.99  
% 26.64/16.99  %Background operators:
% 26.64/16.99  
% 26.64/16.99  
% 26.64/16.99  %Foreground operators:
% 26.64/16.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.64/16.99  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 26.64/16.99  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 26.64/16.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.64/16.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.64/16.99  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 26.64/16.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.64/16.99  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 26.64/16.99  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 26.64/16.99  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 26.64/16.99  tff('#skF_5', type, '#skF_5': $i).
% 26.64/16.99  tff('#skF_2', type, '#skF_2': $i).
% 26.64/16.99  tff('#skF_3', type, '#skF_3': $i).
% 26.64/16.99  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 26.64/16.99  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 26.64/16.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.64/16.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 26.64/16.99  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 26.64/16.99  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 26.64/16.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.64/16.99  tff('#skF_4', type, '#skF_4': $i).
% 26.64/16.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.64/16.99  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 26.64/16.99  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 26.64/16.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.64/16.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 26.64/16.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.64/16.99  
% 26.82/17.04  tff(f_215, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 26.82/17.04  tff(f_95, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 26.82/17.04  tff(f_75, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 26.82/17.04  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 26.82/17.04  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 26.82/17.04  tff(f_190, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 26.82/17.04  tff(f_110, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 26.82/17.04  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 26.82/17.04  tff(f_135, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 26.82/17.04  tff(f_161, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 26.82/17.04  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_50, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_46, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_42, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_40, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_57624, plain, (![C_4232, A_4233, B_4234]: (m1_subset_1(C_4232, k1_zfmisc_1(u1_struct_0(A_4233))) | ~m2_orders_2(C_4232, A_4233, B_4234) | ~m1_orders_1(B_4234, k1_orders_1(u1_struct_0(A_4233))) | ~l1_orders_2(A_4233) | ~v5_orders_2(A_4233) | ~v4_orders_2(A_4233) | ~v3_orders_2(A_4233) | v2_struct_0(A_4233))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.82/17.04  tff(c_57626, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_57624])).
% 26.82/17.04  tff(c_57629, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_42, c_57626])).
% 26.82/17.04  tff(c_57630, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_57629])).
% 26.82/17.04  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k3_orders_2(A_14, B_15, C_16), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 26.82/17.04  tff(c_36, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_6, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 26.82/17.04  tff(c_57633, plain, (![A_4]: (m1_subset_1(A_4, u1_struct_0('#skF_2')) | ~r2_hidden(A_4, '#skF_5'))), inference(resolution, [status(thm)], [c_57630, c_6])).
% 26.82/17.04  tff(c_38, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_215])).
% 26.82/17.04  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 26.82/17.04  tff(c_58078, plain, (![A_4325, D_4326, B_4327, E_4328]: (r3_orders_2(A_4325, k1_funct_1(D_4326, u1_struct_0(A_4325)), B_4327) | ~r2_hidden(B_4327, E_4328) | ~m2_orders_2(E_4328, A_4325, D_4326) | ~m1_orders_1(D_4326, k1_orders_1(u1_struct_0(A_4325))) | ~m1_subset_1(k1_funct_1(D_4326, u1_struct_0(A_4325)), u1_struct_0(A_4325)) | ~m1_subset_1(B_4327, u1_struct_0(A_4325)) | ~l1_orders_2(A_4325) | ~v5_orders_2(A_4325) | ~v4_orders_2(A_4325) | ~v3_orders_2(A_4325) | v2_struct_0(A_4325))), inference(cnfTransformation, [status(thm)], [f_190])).
% 26.82/17.04  tff(c_58202, plain, (![A_4358, D_4359, A_4360, B_4361]: (r3_orders_2(A_4358, k1_funct_1(D_4359, u1_struct_0(A_4358)), '#skF_1'(A_4360, B_4361)) | ~m2_orders_2(B_4361, A_4358, D_4359) | ~m1_orders_1(D_4359, k1_orders_1(u1_struct_0(A_4358))) | ~m1_subset_1(k1_funct_1(D_4359, u1_struct_0(A_4358)), u1_struct_0(A_4358)) | ~m1_subset_1('#skF_1'(A_4360, B_4361), u1_struct_0(A_4358)) | ~l1_orders_2(A_4358) | ~v5_orders_2(A_4358) | ~v4_orders_2(A_4358) | ~v3_orders_2(A_4358) | v2_struct_0(A_4358) | k1_xboole_0=B_4361 | ~m1_subset_1(B_4361, k1_zfmisc_1(A_4360)))), inference(resolution, [status(thm)], [c_2, c_58078])).
% 26.82/17.04  tff(c_58207, plain, (![A_4360, B_4361]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4360, B_4361)) | ~m2_orders_2(B_4361, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_4360, B_4361), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_4361 | ~m1_subset_1(B_4361, k1_zfmisc_1(A_4360)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_58202])).
% 26.82/17.04  tff(c_58210, plain, (![A_4360, B_4361]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4360, B_4361)) | ~m2_orders_2(B_4361, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_4360, B_4361), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_4361 | ~m1_subset_1(B_4361, k1_zfmisc_1(A_4360)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_58207])).
% 26.82/17.04  tff(c_58212, plain, (![A_4362, B_4363]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4362, B_4363)) | ~m2_orders_2(B_4363, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_4362, B_4363), u1_struct_0('#skF_2')) | k1_xboole_0=B_4363 | ~m1_subset_1(B_4363, k1_zfmisc_1(A_4362)))), inference(negUnitSimplification, [status(thm)], [c_54, c_58210])).
% 26.82/17.04  tff(c_58257, plain, (![A_4369, B_4370]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4369, B_4370)) | ~m2_orders_2(B_4370, '#skF_2', '#skF_4') | k1_xboole_0=B_4370 | ~m1_subset_1(B_4370, k1_zfmisc_1(A_4369)) | ~r2_hidden('#skF_1'(A_4369, B_4370), '#skF_5'))), inference(resolution, [status(thm)], [c_57633, c_58212])).
% 26.82/17.04  tff(c_22, plain, (![A_21, B_22, C_23]: (r1_orders_2(A_21, B_22, C_23) | ~r3_orders_2(A_21, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_21)) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 26.82/17.04  tff(c_58259, plain, (![A_4369, B_4370]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4369, B_4370)) | ~m1_subset_1('#skF_1'(A_4369, B_4370), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_4370, '#skF_2', '#skF_4') | k1_xboole_0=B_4370 | ~m1_subset_1(B_4370, k1_zfmisc_1(A_4369)) | ~r2_hidden('#skF_1'(A_4369, B_4370), '#skF_5'))), inference(resolution, [status(thm)], [c_58257, c_22])).
% 26.82/17.04  tff(c_58262, plain, (![A_4369, B_4370]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4369, B_4370)) | ~m1_subset_1('#skF_1'(A_4369, B_4370), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_4370, '#skF_2', '#skF_4') | k1_xboole_0=B_4370 | ~m1_subset_1(B_4370, k1_zfmisc_1(A_4369)) | ~r2_hidden('#skF_1'(A_4369, B_4370), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_58259])).
% 26.82/17.04  tff(c_58287, plain, (![A_4372, B_4373]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4372, B_4373)) | ~m1_subset_1('#skF_1'(A_4372, B_4373), u1_struct_0('#skF_2')) | ~m2_orders_2(B_4373, '#skF_2', '#skF_4') | k1_xboole_0=B_4373 | ~m1_subset_1(B_4373, k1_zfmisc_1(A_4372)) | ~r2_hidden('#skF_1'(A_4372, B_4373), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_58262])).
% 26.82/17.04  tff(c_58336, plain, (![A_4375, B_4376]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4375, B_4376)) | ~m2_orders_2(B_4376, '#skF_2', '#skF_4') | k1_xboole_0=B_4376 | ~m1_subset_1(B_4376, k1_zfmisc_1(A_4375)) | ~r2_hidden('#skF_1'(A_4375, B_4376), '#skF_5'))), inference(resolution, [status(thm)], [c_57633, c_58287])).
% 26.82/17.04  tff(c_57634, plain, (![A_4235]: (m1_subset_1(A_4235, u1_struct_0('#skF_2')) | ~r2_hidden(A_4235, '#skF_5'))), inference(resolution, [status(thm)], [c_57630, c_6])).
% 26.82/17.04  tff(c_74, plain, (![A_111, B_112, C_113]: (r2_orders_2(A_111, B_112, C_113) | C_113=B_112 | ~r1_orders_2(A_111, B_112, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.82/17.04  tff(c_79, plain, (![B_112]: (r2_orders_2('#skF_2', B_112, '#skF_3') | B_112='#skF_3' | ~r1_orders_2('#skF_2', B_112, '#skF_3') | ~m1_subset_1(B_112, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_74])).
% 26.82/17.04  tff(c_83, plain, (![B_112]: (r2_orders_2('#skF_2', B_112, '#skF_3') | B_112='#skF_3' | ~r1_orders_2('#skF_2', B_112, '#skF_3') | ~m1_subset_1(B_112, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79])).
% 26.82/17.04  tff(c_57650, plain, (![A_4235]: (r2_orders_2('#skF_2', A_4235, '#skF_3') | A_4235='#skF_3' | ~r1_orders_2('#skF_2', A_4235, '#skF_3') | ~r2_hidden(A_4235, '#skF_5'))), inference(resolution, [status(thm)], [c_57634, c_83])).
% 26.82/17.04  tff(c_57802, plain, (![A_4266, C_4267, D_4268, B_4269]: (~r2_orders_2(A_4266, C_4267, D_4268) | ~r1_orders_2(A_4266, B_4269, C_4267) | r2_orders_2(A_4266, B_4269, D_4268) | ~m1_subset_1(D_4268, u1_struct_0(A_4266)) | ~m1_subset_1(C_4267, u1_struct_0(A_4266)) | ~m1_subset_1(B_4269, u1_struct_0(A_4266)) | ~l1_orders_2(A_4266) | ~v5_orders_2(A_4266) | ~v4_orders_2(A_4266))), inference(cnfTransformation, [status(thm)], [f_135])).
% 26.82/17.04  tff(c_57810, plain, (![B_4269, A_4235]: (~r1_orders_2('#skF_2', B_4269, A_4235) | r2_orders_2('#skF_2', B_4269, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(A_4235, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4269, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_4235='#skF_3' | ~r1_orders_2('#skF_2', A_4235, '#skF_3') | ~r2_hidden(A_4235, '#skF_5'))), inference(resolution, [status(thm)], [c_57650, c_57802])).
% 26.82/17.04  tff(c_57824, plain, (![B_4269, A_4235]: (~r1_orders_2('#skF_2', B_4269, A_4235) | r2_orders_2('#skF_2', B_4269, '#skF_3') | ~m1_subset_1(A_4235, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4269, u1_struct_0('#skF_2')) | A_4235='#skF_3' | ~r1_orders_2('#skF_2', A_4235, '#skF_3') | ~r2_hidden(A_4235, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_57810])).
% 26.82/17.04  tff(c_58345, plain, (![A_4375, B_4376]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_4375, B_4376), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | '#skF_1'(A_4375, B_4376)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_4375, B_4376), '#skF_3') | ~m2_orders_2(B_4376, '#skF_2', '#skF_4') | k1_xboole_0=B_4376 | ~m1_subset_1(B_4376, k1_zfmisc_1(A_4375)) | ~r2_hidden('#skF_1'(A_4375, B_4376), '#skF_5'))), inference(resolution, [status(thm)], [c_58336, c_57824])).
% 26.82/17.04  tff(c_58359, plain, (![A_4375, B_4376]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_4375, B_4376), u1_struct_0('#skF_2')) | '#skF_1'(A_4375, B_4376)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_4375, B_4376), '#skF_3') | ~m2_orders_2(B_4376, '#skF_2', '#skF_4') | k1_xboole_0=B_4376 | ~m1_subset_1(B_4376, k1_zfmisc_1(A_4375)) | ~r2_hidden('#skF_1'(A_4375, B_4376), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58345])).
% 26.82/17.04  tff(c_58570, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_58359])).
% 26.82/17.04  tff(c_10, plain, (![A_7, C_13]: (~r2_orders_2(A_7, C_13, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.82/17.04  tff(c_58576, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_58570, c_10])).
% 26.82/17.04  tff(c_58586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_58576])).
% 26.82/17.04  tff(c_58588, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_58359])).
% 26.82/17.04  tff(c_57685, plain, (![A_4240, B_4241, C_4242]: (m1_subset_1(k3_orders_2(A_4240, B_4241, C_4242), k1_zfmisc_1(u1_struct_0(A_4240))) | ~m1_subset_1(C_4242, u1_struct_0(A_4240)) | ~m1_subset_1(B_4241, k1_zfmisc_1(u1_struct_0(A_4240))) | ~l1_orders_2(A_4240) | ~v5_orders_2(A_4240) | ~v4_orders_2(A_4240) | ~v3_orders_2(A_4240) | v2_struct_0(A_4240))), inference(cnfTransformation, [status(thm)], [f_75])).
% 26.82/17.04  tff(c_57778, plain, (![A_4256, A_4257, B_4258, C_4259]: (m1_subset_1(A_4256, u1_struct_0(A_4257)) | ~r2_hidden(A_4256, k3_orders_2(A_4257, B_4258, C_4259)) | ~m1_subset_1(C_4259, u1_struct_0(A_4257)) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0(A_4257))) | ~l1_orders_2(A_4257) | ~v5_orders_2(A_4257) | ~v4_orders_2(A_4257) | ~v3_orders_2(A_4257) | v2_struct_0(A_4257))), inference(resolution, [status(thm)], [c_57685, c_6])).
% 26.82/17.04  tff(c_57782, plain, (![A_1, A_4257, B_4258, C_4259]: (m1_subset_1('#skF_1'(A_1, k3_orders_2(A_4257, B_4258, C_4259)), u1_struct_0(A_4257)) | ~m1_subset_1(C_4259, u1_struct_0(A_4257)) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0(A_4257))) | ~l1_orders_2(A_4257) | ~v5_orders_2(A_4257) | ~v4_orders_2(A_4257) | ~v3_orders_2(A_4257) | v2_struct_0(A_4257) | k3_orders_2(A_4257, B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4257, B_4258, C_4259), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_57778])).
% 26.82/17.04  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 26.82/17.04  tff(c_57941, plain, (![B_4284, D_4285, A_4286, C_4287]: (r2_hidden(B_4284, D_4285) | ~r2_hidden(B_4284, k3_orders_2(A_4286, D_4285, C_4287)) | ~m1_subset_1(D_4285, k1_zfmisc_1(u1_struct_0(A_4286))) | ~m1_subset_1(C_4287, u1_struct_0(A_4286)) | ~m1_subset_1(B_4284, u1_struct_0(A_4286)) | ~l1_orders_2(A_4286) | ~v5_orders_2(A_4286) | ~v4_orders_2(A_4286) | ~v3_orders_2(A_4286) | v2_struct_0(A_4286))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.82/17.04  tff(c_58235, plain, (![A_4364, A_4365, D_4366, C_4367]: (r2_hidden('#skF_1'(A_4364, k3_orders_2(A_4365, D_4366, C_4367)), D_4366) | ~m1_subset_1(D_4366, k1_zfmisc_1(u1_struct_0(A_4365))) | ~m1_subset_1(C_4367, u1_struct_0(A_4365)) | ~m1_subset_1('#skF_1'(A_4364, k3_orders_2(A_4365, D_4366, C_4367)), u1_struct_0(A_4365)) | ~l1_orders_2(A_4365) | ~v5_orders_2(A_4365) | ~v4_orders_2(A_4365) | ~v3_orders_2(A_4365) | v2_struct_0(A_4365) | k3_orders_2(A_4365, D_4366, C_4367)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4365, D_4366, C_4367), k1_zfmisc_1(A_4364)))), inference(resolution, [status(thm)], [c_2, c_57941])).
% 26.82/17.04  tff(c_58483, plain, (![A_4391, D_4392, C_4393]: (r2_hidden('#skF_1'(u1_struct_0(A_4391), k3_orders_2(A_4391, D_4392, C_4393)), D_4392) | ~m1_subset_1(D_4392, k1_zfmisc_1(u1_struct_0(A_4391))) | ~m1_subset_1(C_4393, u1_struct_0(A_4391)) | ~l1_orders_2(A_4391) | ~v5_orders_2(A_4391) | ~v4_orders_2(A_4391) | ~v3_orders_2(A_4391) | v2_struct_0(A_4391) | k3_orders_2(A_4391, D_4392, C_4393)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4391, D_4392, C_4393), k1_zfmisc_1(u1_struct_0(A_4391))))), inference(resolution, [status(thm)], [c_4, c_58235])).
% 26.82/17.04  tff(c_34, plain, (![A_54, D_82, B_70, E_84]: (r3_orders_2(A_54, k1_funct_1(D_82, u1_struct_0(A_54)), B_70) | ~r2_hidden(B_70, E_84) | ~m2_orders_2(E_84, A_54, D_82) | ~m1_orders_1(D_82, k1_orders_1(u1_struct_0(A_54))) | ~m1_subset_1(k1_funct_1(D_82, u1_struct_0(A_54)), u1_struct_0(A_54)) | ~m1_subset_1(B_70, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_190])).
% 26.82/17.04  tff(c_73570, plain, (![C_5511, A_5510, D_5509, A_5512, D_5508]: (r3_orders_2(A_5510, k1_funct_1(D_5509, u1_struct_0(A_5510)), '#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511))) | ~m2_orders_2(D_5508, A_5510, D_5509) | ~m1_orders_1(D_5509, k1_orders_1(u1_struct_0(A_5510))) | ~m1_subset_1(k1_funct_1(D_5509, u1_struct_0(A_5510)), u1_struct_0(A_5510)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511)), u1_struct_0(A_5510)) | ~l1_orders_2(A_5510) | ~v5_orders_2(A_5510) | ~v4_orders_2(A_5510) | ~v3_orders_2(A_5510) | v2_struct_0(A_5510) | ~m1_subset_1(D_5508, k1_zfmisc_1(u1_struct_0(A_5512))) | ~m1_subset_1(C_5511, u1_struct_0(A_5512)) | ~l1_orders_2(A_5512) | ~v5_orders_2(A_5512) | ~v4_orders_2(A_5512) | ~v3_orders_2(A_5512) | v2_struct_0(A_5512) | k3_orders_2(A_5512, D_5508, C_5511)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_5512, D_5508, C_5511), k1_zfmisc_1(u1_struct_0(A_5512))))), inference(resolution, [status(thm)], [c_58483, c_34])).
% 26.82/17.04  tff(c_73578, plain, (![A_5512, D_5508, C_5511]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511))) | ~m2_orders_2(D_5508, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(D_5508, k1_zfmisc_1(u1_struct_0(A_5512))) | ~m1_subset_1(C_5511, u1_struct_0(A_5512)) | ~l1_orders_2(A_5512) | ~v5_orders_2(A_5512) | ~v4_orders_2(A_5512) | ~v3_orders_2(A_5512) | v2_struct_0(A_5512) | k3_orders_2(A_5512, D_5508, C_5511)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_5512, D_5508, C_5511), k1_zfmisc_1(u1_struct_0(A_5512))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_73570])).
% 26.82/17.04  tff(c_73584, plain, (![A_5512, D_5508, C_5511]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511))) | ~m2_orders_2(D_5508, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_5512), k3_orders_2(A_5512, D_5508, C_5511)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(D_5508, k1_zfmisc_1(u1_struct_0(A_5512))) | ~m1_subset_1(C_5511, u1_struct_0(A_5512)) | ~l1_orders_2(A_5512) | ~v5_orders_2(A_5512) | ~v4_orders_2(A_5512) | ~v3_orders_2(A_5512) | v2_struct_0(A_5512) | k3_orders_2(A_5512, D_5508, C_5511)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_5512, D_5508, C_5511), k1_zfmisc_1(u1_struct_0(A_5512))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_73578])).
% 26.82/17.04  tff(c_76056, plain, (![A_5626, D_5627, C_5628]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_5626), k3_orders_2(A_5626, D_5627, C_5628))) | ~m2_orders_2(D_5627, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_5626), k3_orders_2(A_5626, D_5627, C_5628)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_5627, k1_zfmisc_1(u1_struct_0(A_5626))) | ~m1_subset_1(C_5628, u1_struct_0(A_5626)) | ~l1_orders_2(A_5626) | ~v5_orders_2(A_5626) | ~v4_orders_2(A_5626) | ~v3_orders_2(A_5626) | v2_struct_0(A_5626) | k3_orders_2(A_5626, D_5627, C_5628)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_5626, D_5627, C_5628), k1_zfmisc_1(u1_struct_0(A_5626))))), inference(negUnitSimplification, [status(thm)], [c_54, c_73584])).
% 26.82/17.04  tff(c_76071, plain, (![B_4258, C_4259]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4258, C_4259))) | ~m2_orders_2(B_4258, '#skF_2', '#skF_4') | ~m1_subset_1(C_4259, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4258, C_4259), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_57782, c_76056])).
% 26.82/17.04  tff(c_76089, plain, (![B_4258, C_4259]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4258, C_4259))) | ~m2_orders_2(B_4258, '#skF_2', '#skF_4') | ~m1_subset_1(C_4259, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4258, C_4259), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_76071])).
% 26.82/17.04  tff(c_76096, plain, (![B_5629, C_5630]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5629, C_5630))) | ~m2_orders_2(B_5629, '#skF_2', '#skF_4') | ~m1_subset_1(C_5630, u1_struct_0('#skF_2')) | ~m1_subset_1(B_5629, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5629, C_5630)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5629, C_5630), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_76089])).
% 26.82/17.04  tff(c_76098, plain, (![B_5629, C_5630]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5629, C_5630))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5629, C_5630)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_5629, '#skF_2', '#skF_4') | ~m1_subset_1(C_5630, u1_struct_0('#skF_2')) | ~m1_subset_1(B_5629, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5629, C_5630)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5629, C_5630), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_76096, c_22])).
% 26.82/17.04  tff(c_76104, plain, (![B_5629, C_5630]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5629, C_5630))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5629, C_5630)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_5629, '#skF_2', '#skF_4') | ~m1_subset_1(C_5630, u1_struct_0('#skF_2')) | ~m1_subset_1(B_5629, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5629, C_5630)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5629, C_5630), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_76098])).
% 26.82/17.04  tff(c_76106, plain, (![B_5631, C_5632]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5631, C_5632))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5631, C_5632)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_5631, '#skF_2', '#skF_4') | ~m1_subset_1(C_5632, u1_struct_0('#skF_2')) | ~m1_subset_1(B_5631, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5631, C_5632)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5631, C_5632), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_76104])).
% 26.82/17.04  tff(c_76121, plain, (![B_4258, C_4259]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4258, C_4259))) | ~m2_orders_2(B_4258, '#skF_2', '#skF_4') | ~m1_subset_1(C_4259, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4258, C_4259), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_57782, c_76106])).
% 26.82/17.04  tff(c_76138, plain, (![B_4258, C_4259]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4258, C_4259))) | ~m2_orders_2(B_4258, '#skF_2', '#skF_4') | ~m1_subset_1(C_4259, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4258, C_4259), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_76121])).
% 26.82/17.04  tff(c_76142, plain, (![B_5633, C_5634]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5633, C_5634))) | ~m2_orders_2(B_5633, '#skF_2', '#skF_4') | ~m1_subset_1(C_5634, u1_struct_0('#skF_2')) | ~m1_subset_1(B_5633, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5633, C_5634)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5633, C_5634), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_76138])).
% 26.82/17.04  tff(c_58013, plain, (![A_4306, B_4307, C_4308, D_4309]: (r2_orders_2(A_4306, B_4307, C_4308) | ~r2_hidden(B_4307, k3_orders_2(A_4306, D_4309, C_4308)) | ~m1_subset_1(D_4309, k1_zfmisc_1(u1_struct_0(A_4306))) | ~m1_subset_1(C_4308, u1_struct_0(A_4306)) | ~m1_subset_1(B_4307, u1_struct_0(A_4306)) | ~l1_orders_2(A_4306) | ~v5_orders_2(A_4306) | ~v4_orders_2(A_4306) | ~v3_orders_2(A_4306) | v2_struct_0(A_4306))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.82/17.04  tff(c_58383, plain, (![A_4379, A_4380, D_4381, C_4382]: (r2_orders_2(A_4379, '#skF_1'(A_4380, k3_orders_2(A_4379, D_4381, C_4382)), C_4382) | ~m1_subset_1(D_4381, k1_zfmisc_1(u1_struct_0(A_4379))) | ~m1_subset_1(C_4382, u1_struct_0(A_4379)) | ~m1_subset_1('#skF_1'(A_4380, k3_orders_2(A_4379, D_4381, C_4382)), u1_struct_0(A_4379)) | ~l1_orders_2(A_4379) | ~v5_orders_2(A_4379) | ~v4_orders_2(A_4379) | ~v3_orders_2(A_4379) | v2_struct_0(A_4379) | k3_orders_2(A_4379, D_4381, C_4382)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4379, D_4381, C_4382), k1_zfmisc_1(A_4380)))), inference(resolution, [status(thm)], [c_2, c_58013])).
% 26.82/17.04  tff(c_58589, plain, (![A_4402, D_4403, C_4404]: (r2_orders_2(A_4402, '#skF_1'(u1_struct_0(A_4402), k3_orders_2(A_4402, D_4403, C_4404)), C_4404) | ~m1_subset_1(D_4403, k1_zfmisc_1(u1_struct_0(A_4402))) | ~m1_subset_1(C_4404, u1_struct_0(A_4402)) | ~l1_orders_2(A_4402) | ~v5_orders_2(A_4402) | ~v4_orders_2(A_4402) | ~v3_orders_2(A_4402) | v2_struct_0(A_4402) | k3_orders_2(A_4402, D_4403, C_4404)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4402, D_4403, C_4404), k1_zfmisc_1(u1_struct_0(A_4402))))), inference(resolution, [status(thm)], [c_4, c_58383])).
% 26.82/17.04  tff(c_12, plain, (![A_7, B_11, C_13]: (r1_orders_2(A_7, B_11, C_13) | ~r2_orders_2(A_7, B_11, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_7)) | ~m1_subset_1(B_11, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.82/17.04  tff(c_59596, plain, (![A_4511, D_4512, C_4513]: (r1_orders_2(A_4511, '#skF_1'(u1_struct_0(A_4511), k3_orders_2(A_4511, D_4512, C_4513)), C_4513) | ~m1_subset_1('#skF_1'(u1_struct_0(A_4511), k3_orders_2(A_4511, D_4512, C_4513)), u1_struct_0(A_4511)) | ~m1_subset_1(D_4512, k1_zfmisc_1(u1_struct_0(A_4511))) | ~m1_subset_1(C_4513, u1_struct_0(A_4511)) | ~l1_orders_2(A_4511) | ~v5_orders_2(A_4511) | ~v4_orders_2(A_4511) | ~v3_orders_2(A_4511) | v2_struct_0(A_4511) | k3_orders_2(A_4511, D_4512, C_4513)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4511, D_4512, C_4513), k1_zfmisc_1(u1_struct_0(A_4511))))), inference(resolution, [status(thm)], [c_58589, c_12])).
% 26.82/17.04  tff(c_59685, plain, (![A_4516, B_4517, C_4518]: (r1_orders_2(A_4516, '#skF_1'(u1_struct_0(A_4516), k3_orders_2(A_4516, B_4517, C_4518)), C_4518) | ~m1_subset_1(C_4518, u1_struct_0(A_4516)) | ~m1_subset_1(B_4517, k1_zfmisc_1(u1_struct_0(A_4516))) | ~l1_orders_2(A_4516) | ~v5_orders_2(A_4516) | ~v4_orders_2(A_4516) | ~v3_orders_2(A_4516) | v2_struct_0(A_4516) | k3_orders_2(A_4516, B_4517, C_4518)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4516, B_4517, C_4518), k1_zfmisc_1(u1_struct_0(A_4516))))), inference(resolution, [status(thm)], [c_57782, c_59596])).
% 26.82/17.04  tff(c_102, plain, (![A_119, B_120, C_121]: (r3_orders_2(A_119, B_120, C_121) | ~r1_orders_2(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_110])).
% 26.82/17.04  tff(c_107, plain, (![B_120]: (r3_orders_2('#skF_2', B_120, '#skF_3') | ~r1_orders_2('#skF_2', B_120, '#skF_3') | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_102])).
% 26.82/17.04  tff(c_111, plain, (![B_120]: (r3_orders_2('#skF_2', B_120, '#skF_3') | ~r1_orders_2('#skF_2', B_120, '#skF_3') | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_107])).
% 26.82/17.04  tff(c_113, plain, (![B_122]: (r3_orders_2('#skF_2', B_122, '#skF_3') | ~r1_orders_2('#skF_2', B_122, '#skF_3') | ~m1_subset_1(B_122, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_111])).
% 26.82/17.04  tff(c_122, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_113])).
% 26.82/17.04  tff(c_123, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_122])).
% 26.82/17.04  tff(c_138, plain, (![C_127, A_128, B_129]: (m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~m2_orders_2(C_127, A_128, B_129) | ~m1_orders_1(B_129, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_95])).
% 26.82/17.04  tff(c_140, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_138])).
% 26.82/17.04  tff(c_143, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_42, c_140])).
% 26.82/17.04  tff(c_144, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_143])).
% 26.82/17.04  tff(c_212, plain, (![A_138, B_139, C_140]: (m1_subset_1(k3_orders_2(A_138, B_139, C_140), k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_75])).
% 26.82/17.04  tff(c_290, plain, (![A_151, A_152, B_153, C_154]: (m1_subset_1(A_151, u1_struct_0(A_152)) | ~r2_hidden(A_151, k3_orders_2(A_152, B_153, C_154)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_212, c_6])).
% 26.82/17.04  tff(c_294, plain, (![A_1, A_152, B_153, C_154]: (m1_subset_1('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), u1_struct_0(A_152)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_290])).
% 26.82/17.04  tff(c_335, plain, (![B_165, D_166, A_167, C_168]: (r2_hidden(B_165, D_166) | ~r2_hidden(B_165, k3_orders_2(A_167, D_166, C_168)) | ~m1_subset_1(D_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(C_168, u1_struct_0(A_167)) | ~m1_subset_1(B_165, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.82/17.04  tff(c_708, plain, (![A_264, A_265, D_266, C_267]: (r2_hidden('#skF_1'(A_264, k3_orders_2(A_265, D_266, C_267)), D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_subset_1(C_267, u1_struct_0(A_265)) | ~m1_subset_1('#skF_1'(A_264, k3_orders_2(A_265, D_266, C_267)), u1_struct_0(A_265)) | ~l1_orders_2(A_265) | ~v5_orders_2(A_265) | ~v4_orders_2(A_265) | ~v3_orders_2(A_265) | v2_struct_0(A_265) | k3_orders_2(A_265, D_266, C_267)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_265, D_266, C_267), k1_zfmisc_1(A_264)))), inference(resolution, [status(thm)], [c_2, c_335])).
% 26.82/17.04  tff(c_1379, plain, (![A_339, A_340, B_341, C_342]: (r2_hidden('#skF_1'(A_339, k3_orders_2(A_340, B_341, C_342)), B_341) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_340))) | ~l1_orders_2(A_340) | ~v5_orders_2(A_340) | ~v4_orders_2(A_340) | ~v3_orders_2(A_340) | v2_struct_0(A_340) | k3_orders_2(A_340, B_341, C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_340, B_341, C_342), k1_zfmisc_1(A_339)))), inference(resolution, [status(thm)], [c_294, c_708])).
% 26.82/17.04  tff(c_147, plain, (![A_4]: (m1_subset_1(A_4, u1_struct_0('#skF_2')) | ~r2_hidden(A_4, '#skF_5'))), inference(resolution, [status(thm)], [c_144, c_6])).
% 26.82/17.04  tff(c_713, plain, (![A_264, D_266, C_267]: (r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_267, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_266, C_267)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_266, C_267), k1_zfmisc_1(A_264)) | ~r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_708])).
% 26.82/17.04  tff(c_720, plain, (![A_264, D_266, C_267]: (r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_267, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_266, C_267)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_266, C_267), k1_zfmisc_1(A_264)) | ~r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_713])).
% 26.82/17.04  tff(c_721, plain, (![A_264, D_266, C_267]: (r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_267, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_266, C_267)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_266, C_267), k1_zfmisc_1(A_264)) | ~r2_hidden('#skF_1'(A_264, k3_orders_2('#skF_2', D_266, C_267)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_720])).
% 26.82/17.04  tff(c_1382, plain, (![A_339, C_342]: (r2_hidden('#skF_1'(A_339, k3_orders_2('#skF_2', '#skF_5', C_342)), '#skF_5') | ~m1_subset_1(C_342, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_342), k1_zfmisc_1(A_339)))), inference(resolution, [status(thm)], [c_1379, c_721])).
% 26.82/17.04  tff(c_1404, plain, (![A_339, C_342]: (r2_hidden('#skF_1'(A_339, k3_orders_2('#skF_2', '#skF_5', C_342)), '#skF_5') | ~m1_subset_1(C_342, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_342), k1_zfmisc_1(A_339)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_1382])).
% 26.82/17.04  tff(c_1405, plain, (![A_339, C_342]: (r2_hidden('#skF_1'(A_339, k3_orders_2('#skF_2', '#skF_5', C_342)), '#skF_5') | ~m1_subset_1(C_342, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_342), k1_zfmisc_1(A_339)))), inference(negUnitSimplification, [status(thm)], [c_54, c_1404])).
% 26.82/17.04  tff(c_969, plain, (![A_292, D_293, C_294]: (r2_hidden('#skF_1'(u1_struct_0(A_292), k3_orders_2(A_292, D_293, C_294)), D_293) | ~m1_subset_1(D_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~m1_subset_1(C_294, u1_struct_0(A_292)) | ~l1_orders_2(A_292) | ~v5_orders_2(A_292) | ~v4_orders_2(A_292) | ~v3_orders_2(A_292) | v2_struct_0(A_292) | k3_orders_2(A_292, D_293, C_294)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_292, D_293, C_294), k1_zfmisc_1(u1_struct_0(A_292))))), inference(resolution, [status(thm)], [c_4, c_708])).
% 26.82/17.04  tff(c_54814, plain, (![D_4113, A_4112, C_4109, A_4111, D_4110]: (r3_orders_2(A_4111, k1_funct_1(D_4110, u1_struct_0(A_4111)), '#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109))) | ~m2_orders_2(D_4113, A_4111, D_4110) | ~m1_orders_1(D_4110, k1_orders_1(u1_struct_0(A_4111))) | ~m1_subset_1(k1_funct_1(D_4110, u1_struct_0(A_4111)), u1_struct_0(A_4111)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109)), u1_struct_0(A_4111)) | ~l1_orders_2(A_4111) | ~v5_orders_2(A_4111) | ~v4_orders_2(A_4111) | ~v3_orders_2(A_4111) | v2_struct_0(A_4111) | ~m1_subset_1(D_4113, k1_zfmisc_1(u1_struct_0(A_4112))) | ~m1_subset_1(C_4109, u1_struct_0(A_4112)) | ~l1_orders_2(A_4112) | ~v5_orders_2(A_4112) | ~v4_orders_2(A_4112) | ~v3_orders_2(A_4112) | v2_struct_0(A_4112) | k3_orders_2(A_4112, D_4113, C_4109)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4112, D_4113, C_4109), k1_zfmisc_1(u1_struct_0(A_4112))))), inference(resolution, [status(thm)], [c_969, c_34])).
% 26.82/17.04  tff(c_54822, plain, (![A_4112, D_4113, C_4109]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109))) | ~m2_orders_2(D_4113, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(D_4113, k1_zfmisc_1(u1_struct_0(A_4112))) | ~m1_subset_1(C_4109, u1_struct_0(A_4112)) | ~l1_orders_2(A_4112) | ~v5_orders_2(A_4112) | ~v4_orders_2(A_4112) | ~v3_orders_2(A_4112) | v2_struct_0(A_4112) | k3_orders_2(A_4112, D_4113, C_4109)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4112, D_4113, C_4109), k1_zfmisc_1(u1_struct_0(A_4112))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_54814])).
% 26.82/17.04  tff(c_54828, plain, (![A_4112, D_4113, C_4109]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109))) | ~m2_orders_2(D_4113, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_4112), k3_orders_2(A_4112, D_4113, C_4109)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(D_4113, k1_zfmisc_1(u1_struct_0(A_4112))) | ~m1_subset_1(C_4109, u1_struct_0(A_4112)) | ~l1_orders_2(A_4112) | ~v5_orders_2(A_4112) | ~v4_orders_2(A_4112) | ~v3_orders_2(A_4112) | v2_struct_0(A_4112) | k3_orders_2(A_4112, D_4113, C_4109)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4112, D_4113, C_4109), k1_zfmisc_1(u1_struct_0(A_4112))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_54822])).
% 26.82/17.04  tff(c_56758, plain, (![A_4210, D_4211, C_4212]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_4210), k3_orders_2(A_4210, D_4211, C_4212))) | ~m2_orders_2(D_4211, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_4210), k3_orders_2(A_4210, D_4211, C_4212)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_4211, k1_zfmisc_1(u1_struct_0(A_4210))) | ~m1_subset_1(C_4212, u1_struct_0(A_4210)) | ~l1_orders_2(A_4210) | ~v5_orders_2(A_4210) | ~v4_orders_2(A_4210) | ~v3_orders_2(A_4210) | v2_struct_0(A_4210) | k3_orders_2(A_4210, D_4211, C_4212)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4210, D_4211, C_4212), k1_zfmisc_1(u1_struct_0(A_4210))))), inference(negUnitSimplification, [status(thm)], [c_54, c_54828])).
% 26.82/17.04  tff(c_56773, plain, (![B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_294, c_56758])).
% 26.82/17.04  tff(c_56791, plain, (![B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_56773])).
% 26.82/17.04  tff(c_56798, plain, (![B_4213, C_4214]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4213, C_4214))) | ~m2_orders_2(B_4213, '#skF_2', '#skF_4') | ~m1_subset_1(C_4214, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4213, C_4214)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4213, C_4214), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_56791])).
% 26.82/17.04  tff(c_56800, plain, (![B_4213, C_4214]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4213, C_4214))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4213, C_4214)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_4213, '#skF_2', '#skF_4') | ~m1_subset_1(C_4214, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4213, C_4214)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4213, C_4214), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_56798, c_22])).
% 26.82/17.04  tff(c_56806, plain, (![B_4213, C_4214]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4213, C_4214))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4213, C_4214)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_4213, '#skF_2', '#skF_4') | ~m1_subset_1(C_4214, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4213, C_4214)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4213, C_4214), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_56800])).
% 26.82/17.04  tff(c_56808, plain, (![B_4215, C_4216]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4215, C_4216))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4215, C_4216)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_4215, '#skF_2', '#skF_4') | ~m1_subset_1(C_4216, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4215, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4215, C_4216)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4215, C_4216), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_56806])).
% 26.82/17.04  tff(c_56823, plain, (![B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_294, c_56808])).
% 26.82/17.04  tff(c_56840, plain, (![B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_56823])).
% 26.82/17.04  tff(c_56844, plain, (![B_4217, C_4218]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4217, C_4218))) | ~m2_orders_2(B_4217, '#skF_2', '#skF_4') | ~m1_subset_1(C_4218, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4217, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4217, C_4218)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4217, C_4218), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_56840])).
% 26.82/17.04  tff(c_445, plain, (![A_185, B_186, C_187, D_188]: (r2_orders_2(A_185, B_186, C_187) | ~r2_hidden(B_186, k3_orders_2(A_185, D_188, C_187)) | ~m1_subset_1(D_188, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v5_orders_2(A_185) | ~v4_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_161])).
% 26.82/17.04  tff(c_914, plain, (![A_280, A_281, D_282, C_283]: (r2_orders_2(A_280, '#skF_1'(A_281, k3_orders_2(A_280, D_282, C_283)), C_283) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_subset_1(C_283, u1_struct_0(A_280)) | ~m1_subset_1('#skF_1'(A_281, k3_orders_2(A_280, D_282, C_283)), u1_struct_0(A_280)) | ~l1_orders_2(A_280) | ~v5_orders_2(A_280) | ~v4_orders_2(A_280) | ~v3_orders_2(A_280) | v2_struct_0(A_280) | k3_orders_2(A_280, D_282, C_283)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_280, D_282, C_283), k1_zfmisc_1(A_281)))), inference(resolution, [status(thm)], [c_2, c_445])).
% 26.82/17.04  tff(c_919, plain, (![A_281, D_282, C_283]: (r2_orders_2('#skF_2', '#skF_1'(A_281, k3_orders_2('#skF_2', D_282, C_283)), C_283) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_283, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_282, C_283)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_282, C_283), k1_zfmisc_1(A_281)) | ~r2_hidden('#skF_1'(A_281, k3_orders_2('#skF_2', D_282, C_283)), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_914])).
% 26.82/17.04  tff(c_926, plain, (![A_281, D_282, C_283]: (r2_orders_2('#skF_2', '#skF_1'(A_281, k3_orders_2('#skF_2', D_282, C_283)), C_283) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_283, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_282, C_283)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_282, C_283), k1_zfmisc_1(A_281)) | ~r2_hidden('#skF_1'(A_281, k3_orders_2('#skF_2', D_282, C_283)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_919])).
% 26.82/17.04  tff(c_1354, plain, (![A_336, D_337, C_338]: (r2_orders_2('#skF_2', '#skF_1'(A_336, k3_orders_2('#skF_2', D_337, C_338)), C_338) | ~m1_subset_1(D_337, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_338, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_337, C_338)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_337, C_338), k1_zfmisc_1(A_336)) | ~r2_hidden('#skF_1'(A_336, k3_orders_2('#skF_2', D_337, C_338)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_926])).
% 26.82/17.04  tff(c_1366, plain, (![A_336, D_337, C_338]: (r1_orders_2('#skF_2', '#skF_1'(A_336, k3_orders_2('#skF_2', D_337, C_338)), C_338) | ~m1_subset_1('#skF_1'(A_336, k3_orders_2('#skF_2', D_337, C_338)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~m1_subset_1(D_337, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_338, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_337, C_338)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_337, C_338), k1_zfmisc_1(A_336)) | ~r2_hidden('#skF_1'(A_336, k3_orders_2('#skF_2', D_337, C_338)), '#skF_5'))), inference(resolution, [status(thm)], [c_1354, c_12])).
% 26.82/17.04  tff(c_37283, plain, (![A_2896, D_2897, C_2898]: (r1_orders_2('#skF_2', '#skF_1'(A_2896, k3_orders_2('#skF_2', D_2897, C_2898)), C_2898) | ~m1_subset_1('#skF_1'(A_2896, k3_orders_2('#skF_2', D_2897, C_2898)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_2897, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_2898, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_2897, C_2898)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_2897, C_2898), k1_zfmisc_1(A_2896)) | ~r2_hidden('#skF_1'(A_2896, k3_orders_2('#skF_2', D_2897, C_2898)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1366])).
% 26.82/17.04  tff(c_37286, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154)), C_154) | ~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154)), '#skF_5') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_294, c_37283])).
% 26.82/17.04  tff(c_37295, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154)), C_154) | ~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154)), '#skF_5') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_37286])).
% 26.82/17.04  tff(c_37299, plain, (![A_2899, B_2900, C_2901]: (r1_orders_2('#skF_2', '#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, C_2901)), C_2901) | ~r2_hidden('#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, C_2901)), '#skF_5') | ~m1_subset_1(C_2901, u1_struct_0('#skF_2')) | ~m1_subset_1(B_2900, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_2900, C_2901)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_2900, C_2901), k1_zfmisc_1(A_2899)))), inference(negUnitSimplification, [status(thm)], [c_54, c_37295])).
% 26.82/17.04  tff(c_148, plain, (![A_130]: (m1_subset_1(A_130, u1_struct_0('#skF_2')) | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_144, c_6])).
% 26.82/17.04  tff(c_8, plain, (![A_7, B_11, C_13]: (r2_orders_2(A_7, B_11, C_13) | C_13=B_11 | ~r1_orders_2(A_7, B_11, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_7)) | ~m1_subset_1(B_11, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 26.82/17.04  tff(c_158, plain, (![B_11, A_130]: (r2_orders_2('#skF_2', B_11, A_130) | B_11=A_130 | ~r1_orders_2('#skF_2', B_11, A_130) | ~m1_subset_1(B_11, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_148, c_8])).
% 26.82/17.04  tff(c_216, plain, (![B_141, A_142]: (r2_orders_2('#skF_2', B_141, A_142) | B_141=A_142 | ~r1_orders_2('#skF_2', B_141, A_142) | ~m1_subset_1(B_141, u1_struct_0('#skF_2')) | ~r2_hidden(A_142, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_158])).
% 26.82/17.04  tff(c_226, plain, (![A_142]: (r2_orders_2('#skF_2', '#skF_3', A_142) | A_142='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_142) | ~r2_hidden(A_142, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_216])).
% 26.82/17.04  tff(c_309, plain, (![A_161, C_162, D_163, B_164]: (~r2_orders_2(A_161, C_162, D_163) | ~r1_orders_2(A_161, B_164, C_162) | r2_orders_2(A_161, B_164, D_163) | ~m1_subset_1(D_163, u1_struct_0(A_161)) | ~m1_subset_1(C_162, u1_struct_0(A_161)) | ~m1_subset_1(B_164, u1_struct_0(A_161)) | ~l1_orders_2(A_161) | ~v5_orders_2(A_161) | ~v4_orders_2(A_161))), inference(cnfTransformation, [status(thm)], [f_135])).
% 26.82/17.04  tff(c_315, plain, (![B_164, A_142]: (~r1_orders_2('#skF_2', B_164, '#skF_3') | r2_orders_2('#skF_2', B_164, A_142) | ~m1_subset_1(A_142, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_164, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_142='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_142) | ~r2_hidden(A_142, '#skF_5'))), inference(resolution, [status(thm)], [c_226, c_309])).
% 26.82/17.04  tff(c_341, plain, (![B_171, A_172]: (~r1_orders_2('#skF_2', B_171, '#skF_3') | r2_orders_2('#skF_2', B_171, A_172) | ~m1_subset_1(A_172, u1_struct_0('#skF_2')) | ~m1_subset_1(B_171, u1_struct_0('#skF_2')) | A_172='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_172) | ~r2_hidden(A_172, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_315])).
% 26.82/17.04  tff(c_356, plain, (![B_173, A_174]: (~r1_orders_2('#skF_2', B_173, '#skF_3') | r2_orders_2('#skF_2', B_173, A_174) | ~m1_subset_1(B_173, u1_struct_0('#skF_2')) | A_174='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_174) | ~r2_hidden(A_174, '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_341])).
% 26.82/17.04  tff(c_378, plain, (![A_177, A_178]: (~r1_orders_2('#skF_2', A_177, '#skF_3') | r2_orders_2('#skF_2', A_177, A_178) | A_178='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_178) | ~r2_hidden(A_178, '#skF_5') | ~r2_hidden(A_177, '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_356])).
% 26.82/17.04  tff(c_385, plain, (![A_178]: (~m1_subset_1(A_178, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r1_orders_2('#skF_2', A_178, '#skF_3') | A_178='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_178) | ~r2_hidden(A_178, '#skF_5'))), inference(resolution, [status(thm)], [c_378, c_10])).
% 26.82/17.04  tff(c_395, plain, (![A_179]: (~m1_subset_1(A_179, u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', A_179, '#skF_3') | A_179='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_179) | ~r2_hidden(A_179, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_385])).
% 26.82/17.04  tff(c_411, plain, (![A_4]: (~r1_orders_2('#skF_2', A_4, '#skF_3') | A_4='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_4) | ~r2_hidden(A_4, '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_395])).
% 26.82/17.04  tff(c_37336, plain, (![A_2899, B_2900]: ('#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3'))) | ~r2_hidden('#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_2900, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_2900, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_2900, '#skF_3'), k1_zfmisc_1(A_2899)))), inference(resolution, [status(thm)], [c_37299, c_411])).
% 26.82/17.04  tff(c_37366, plain, (![A_2899, B_2900]: ('#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3'))) | ~r2_hidden('#skF_1'(A_2899, k3_orders_2('#skF_2', B_2900, '#skF_3')), '#skF_5') | ~m1_subset_1(B_2900, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_2900, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_2900, '#skF_3'), k1_zfmisc_1(A_2899)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_37336])).
% 26.82/17.04  tff(c_56864, plain, (![B_4217]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4217, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4217, '#skF_3')), '#skF_5') | ~m2_orders_2(B_4217, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_4217, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4217, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4217, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_56844, c_37366])).
% 26.82/17.04  tff(c_56945, plain, (![B_4219]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4219, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4219, '#skF_3')), '#skF_5') | ~m2_orders_2(B_4219, '#skF_2', '#skF_4') | ~m1_subset_1(B_4219, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4219, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4219, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56864])).
% 26.82/17.04  tff(c_56953, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1405, c_56945])).
% 26.82/17.04  tff(c_56963, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_144, c_40, c_56953])).
% 26.82/17.04  tff(c_56964, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_56963])).
% 26.82/17.04  tff(c_56969, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_56964])).
% 26.82/17.04  tff(c_56972, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_56969])).
% 26.82/17.04  tff(c_56975, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_56972])).
% 26.82/17.04  tff(c_56977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_56975])).
% 26.82/17.04  tff(c_56979, plain, (m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_56964])).
% 26.82/17.04  tff(c_516, plain, (![A_213, D_214, B_215, E_216]: (r3_orders_2(A_213, k1_funct_1(D_214, u1_struct_0(A_213)), B_215) | ~r2_hidden(B_215, E_216) | ~m2_orders_2(E_216, A_213, D_214) | ~m1_orders_1(D_214, k1_orders_1(u1_struct_0(A_213))) | ~m1_subset_1(k1_funct_1(D_214, u1_struct_0(A_213)), u1_struct_0(A_213)) | ~m1_subset_1(B_215, u1_struct_0(A_213)) | ~l1_orders_2(A_213) | ~v5_orders_2(A_213) | ~v4_orders_2(A_213) | ~v3_orders_2(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_190])).
% 26.82/17.04  tff(c_661, plain, (![A_255, D_256, A_257, B_258]: (r3_orders_2(A_255, k1_funct_1(D_256, u1_struct_0(A_255)), '#skF_1'(A_257, B_258)) | ~m2_orders_2(B_258, A_255, D_256) | ~m1_orders_1(D_256, k1_orders_1(u1_struct_0(A_255))) | ~m1_subset_1(k1_funct_1(D_256, u1_struct_0(A_255)), u1_struct_0(A_255)) | ~m1_subset_1('#skF_1'(A_257, B_258), u1_struct_0(A_255)) | ~l1_orders_2(A_255) | ~v5_orders_2(A_255) | ~v4_orders_2(A_255) | ~v3_orders_2(A_255) | v2_struct_0(A_255) | k1_xboole_0=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(A_257)))), inference(resolution, [status(thm)], [c_2, c_516])).
% 26.82/17.04  tff(c_666, plain, (![A_257, B_258]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_257, B_258)) | ~m2_orders_2(B_258, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_257, B_258), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(A_257)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_661])).
% 26.82/17.04  tff(c_669, plain, (![A_257, B_258]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_257, B_258)) | ~m2_orders_2(B_258, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_257, B_258), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(A_257)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_666])).
% 26.82/17.04  tff(c_671, plain, (![A_259, B_260]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_259, B_260)) | ~m2_orders_2(B_260, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_259, B_260), u1_struct_0('#skF_2')) | k1_xboole_0=B_260 | ~m1_subset_1(B_260, k1_zfmisc_1(A_259)))), inference(negUnitSimplification, [status(thm)], [c_54, c_669])).
% 26.82/17.04  tff(c_701, plain, (![A_262, B_263]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_262, B_263)) | ~m2_orders_2(B_263, '#skF_2', '#skF_4') | k1_xboole_0=B_263 | ~m1_subset_1(B_263, k1_zfmisc_1(A_262)) | ~r2_hidden('#skF_1'(A_262, B_263), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_671])).
% 26.82/17.04  tff(c_703, plain, (![A_262, B_263]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_262, B_263)) | ~m1_subset_1('#skF_1'(A_262, B_263), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_263, '#skF_2', '#skF_4') | k1_xboole_0=B_263 | ~m1_subset_1(B_263, k1_zfmisc_1(A_262)) | ~r2_hidden('#skF_1'(A_262, B_263), '#skF_5'))), inference(resolution, [status(thm)], [c_701, c_22])).
% 26.82/17.04  tff(c_706, plain, (![A_262, B_263]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_262, B_263)) | ~m1_subset_1('#skF_1'(A_262, B_263), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_263, '#skF_2', '#skF_4') | k1_xboole_0=B_263 | ~m1_subset_1(B_263, k1_zfmisc_1(A_262)) | ~r2_hidden('#skF_1'(A_262, B_263), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_703])).
% 26.82/17.04  tff(c_772, plain, (![A_270, B_271]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_270, B_271)) | ~m1_subset_1('#skF_1'(A_270, B_271), u1_struct_0('#skF_2')) | ~m2_orders_2(B_271, '#skF_2', '#skF_4') | k1_xboole_0=B_271 | ~m1_subset_1(B_271, k1_zfmisc_1(A_270)) | ~r2_hidden('#skF_1'(A_270, B_271), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_706])).
% 26.82/17.04  tff(c_795, plain, (![A_272, B_273]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_272, B_273)) | ~m2_orders_2(B_273, '#skF_2', '#skF_4') | k1_xboole_0=B_273 | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)) | ~r2_hidden('#skF_1'(A_272, B_273), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_772])).
% 26.82/17.04  tff(c_164, plain, (![A_130]: (r2_orders_2('#skF_2', A_130, '#skF_3') | A_130='#skF_3' | ~r1_orders_2('#skF_2', A_130, '#skF_3') | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_148, c_83])).
% 26.82/17.04  tff(c_317, plain, (![B_164, A_130]: (~r1_orders_2('#skF_2', B_164, A_130) | r2_orders_2('#skF_2', B_164, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(A_130, u1_struct_0('#skF_2')) | ~m1_subset_1(B_164, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_130='#skF_3' | ~r1_orders_2('#skF_2', A_130, '#skF_3') | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_164, c_309])).
% 26.82/17.04  tff(c_331, plain, (![B_164, A_130]: (~r1_orders_2('#skF_2', B_164, A_130) | r2_orders_2('#skF_2', B_164, '#skF_3') | ~m1_subset_1(A_130, u1_struct_0('#skF_2')) | ~m1_subset_1(B_164, u1_struct_0('#skF_2')) | A_130='#skF_3' | ~r1_orders_2('#skF_2', A_130, '#skF_3') | ~r2_hidden(A_130, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_317])).
% 26.82/17.04  tff(c_804, plain, (![A_272, B_273]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_272, B_273), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | '#skF_1'(A_272, B_273)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_272, B_273), '#skF_3') | ~m2_orders_2(B_273, '#skF_2', '#skF_4') | k1_xboole_0=B_273 | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)) | ~r2_hidden('#skF_1'(A_272, B_273), '#skF_5'))), inference(resolution, [status(thm)], [c_795, c_331])).
% 26.82/17.04  tff(c_818, plain, (![A_272, B_273]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_272, B_273), u1_struct_0('#skF_2')) | '#skF_1'(A_272, B_273)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_272, B_273), '#skF_3') | ~m2_orders_2(B_273, '#skF_2', '#skF_4') | k1_xboole_0=B_273 | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)) | ~r2_hidden('#skF_1'(A_272, B_273), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_804])).
% 26.82/17.04  tff(c_1018, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_818])).
% 26.82/17.04  tff(c_1022, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1018, c_12])).
% 26.82/17.04  tff(c_1030, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1022])).
% 26.82/17.04  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1030])).
% 26.82/17.04  tff(c_1034, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_818])).
% 26.82/17.04  tff(c_1225, plain, (![A_321, D_322, A_323, B_324]: (r1_orders_2(A_321, k1_funct_1(D_322, u1_struct_0(A_321)), '#skF_1'(A_323, B_324)) | ~m2_orders_2(B_324, A_321, D_322) | ~m1_orders_1(D_322, k1_orders_1(u1_struct_0(A_321))) | ~m1_subset_1(k1_funct_1(D_322, u1_struct_0(A_321)), u1_struct_0(A_321)) | ~m1_subset_1('#skF_1'(A_323, B_324), u1_struct_0(A_321)) | ~l1_orders_2(A_321) | ~v5_orders_2(A_321) | ~v4_orders_2(A_321) | ~v3_orders_2(A_321) | v2_struct_0(A_321) | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(A_323)))), inference(resolution, [status(thm)], [c_661, c_22])).
% 26.82/17.04  tff(c_84, plain, (![B_114]: (r2_orders_2('#skF_2', B_114, '#skF_3') | B_114='#skF_3' | ~r1_orders_2('#skF_2', B_114, '#skF_3') | ~m1_subset_1(B_114, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79])).
% 26.82/17.04  tff(c_92, plain, (![B_2]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_84])).
% 26.82/17.04  tff(c_319, plain, (![B_164, B_2]: (~r1_orders_2('#skF_2', B_164, '#skF_1'(u1_struct_0('#skF_2'), B_2)) | r2_orders_2('#skF_2', B_164, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2), u1_struct_0('#skF_2')) | ~m1_subset_1(B_164, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_92, c_309])).
% 26.82/17.04  tff(c_334, plain, (![B_164, B_2]: (~r1_orders_2('#skF_2', B_164, '#skF_1'(u1_struct_0('#skF_2'), B_2)) | r2_orders_2('#skF_2', B_164, '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2), u1_struct_0('#skF_2')) | ~m1_subset_1(B_164, u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_319])).
% 26.82/17.04  tff(c_1228, plain, (![D_322, B_324]: (r2_orders_2('#skF_2', k1_funct_1(D_322, u1_struct_0('#skF_2')), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_324)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_324), '#skF_3') | ~m2_orders_2(B_324, '#skF_2', D_322) | ~m1_orders_1(D_322, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_322, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_324), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1225, c_334])).
% 26.82/17.04  tff(c_1245, plain, (![D_322, B_324]: (r2_orders_2('#skF_2', k1_funct_1(D_322, u1_struct_0('#skF_2')), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_324)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_324), '#skF_3') | ~m2_orders_2(B_324, '#skF_2', D_322) | ~m1_orders_1(D_322, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_322, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_324), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1228])).
% 26.82/17.04  tff(c_39066, plain, (![D_3008, B_3009]: (r2_orders_2('#skF_2', k1_funct_1(D_3008, u1_struct_0('#skF_2')), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_3009)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_3009), '#skF_3') | ~m2_orders_2(B_3009, '#skF_2', D_3008) | ~m1_orders_1(D_3008, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_3008, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_3009), u1_struct_0('#skF_2')) | k1_xboole_0=B_3009 | ~m1_subset_1(B_3009, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1245])).
% 26.82/17.04  tff(c_39068, plain, (r2_orders_2('#skF_2', k1_funct_1('#skF_4', u1_struct_0('#skF_2')), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), '#skF_3') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_39066])).
% 26.82/17.04  tff(c_39071, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_44, c_38, c_42, c_38, c_39068])).
% 26.82/17.04  tff(c_39072, plain, ('#skF_1'(u1_struct_0('#skF_2'), '#skF_5')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1034, c_39071])).
% 26.82/17.04  tff(c_39073, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_39072])).
% 26.82/17.04  tff(c_39079, plain, (k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4, c_39073])).
% 26.82/17.04  tff(c_39083, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_39079])).
% 26.82/17.04  tff(c_39173, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_36])).
% 26.82/17.04  tff(c_717, plain, (![A_1, A_152, B_153, C_154]: (r2_hidden('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), B_153) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_294, c_708])).
% 26.82/17.04  tff(c_39130, plain, (![A_1, A_152, B_153, C_154]: (r2_hidden('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), B_153) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_717])).
% 26.82/17.04  tff(c_39158, plain, (![A_1, A_152, B_153, C_154]: (m1_subset_1('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), u1_struct_0(A_152)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_294])).
% 26.82/17.04  tff(c_1406, plain, (![C_342, B_341, A_339, A_340, D_82, A_54]: (r3_orders_2(A_54, k1_funct_1(D_82, u1_struct_0(A_54)), '#skF_1'(A_339, k3_orders_2(A_340, B_341, C_342))) | ~m2_orders_2(B_341, A_54, D_82) | ~m1_orders_1(D_82, k1_orders_1(u1_struct_0(A_54))) | ~m1_subset_1(k1_funct_1(D_82, u1_struct_0(A_54)), u1_struct_0(A_54)) | ~m1_subset_1('#skF_1'(A_339, k3_orders_2(A_340, B_341, C_342)), u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_340))) | ~l1_orders_2(A_340) | ~v5_orders_2(A_340) | ~v4_orders_2(A_340) | ~v3_orders_2(A_340) | v2_struct_0(A_340) | k3_orders_2(A_340, B_341, C_342)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_340, B_341, C_342), k1_zfmisc_1(A_339)))), inference(resolution, [status(thm)], [c_1379, c_34])).
% 26.82/17.04  tff(c_43069, plain, (![B_3371, D_3372, A_3376, C_3375, A_3373, A_3374]: (r3_orders_2(A_3373, k1_funct_1(D_3372, u1_struct_0(A_3373)), '#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375))) | ~m2_orders_2(B_3371, A_3373, D_3372) | ~m1_orders_1(D_3372, k1_orders_1(u1_struct_0(A_3373))) | ~m1_subset_1(k1_funct_1(D_3372, u1_struct_0(A_3373)), u1_struct_0(A_3373)) | ~m1_subset_1('#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375)), u1_struct_0(A_3373)) | ~l1_orders_2(A_3373) | ~v5_orders_2(A_3373) | ~v4_orders_2(A_3373) | ~v3_orders_2(A_3373) | v2_struct_0(A_3373) | ~m1_subset_1(C_3375, u1_struct_0(A_3374)) | ~m1_subset_1(B_3371, k1_zfmisc_1(u1_struct_0(A_3374))) | ~l1_orders_2(A_3374) | ~v5_orders_2(A_3374) | ~v4_orders_2(A_3374) | ~v3_orders_2(A_3374) | v2_struct_0(A_3374) | k3_orders_2(A_3374, B_3371, C_3375)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3374, B_3371, C_3375), k1_zfmisc_1(A_3376)))), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_1406])).
% 26.82/17.04  tff(c_43077, plain, (![A_3376, A_3374, B_3371, C_3375]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375))) | ~m2_orders_2(B_3371, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_3375, u1_struct_0(A_3374)) | ~m1_subset_1(B_3371, k1_zfmisc_1(u1_struct_0(A_3374))) | ~l1_orders_2(A_3374) | ~v5_orders_2(A_3374) | ~v4_orders_2(A_3374) | ~v3_orders_2(A_3374) | v2_struct_0(A_3374) | k3_orders_2(A_3374, B_3371, C_3375)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3374, B_3371, C_3375), k1_zfmisc_1(A_3376)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_43069])).
% 26.82/17.04  tff(c_43083, plain, (![A_3376, A_3374, B_3371, C_3375]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375))) | ~m2_orders_2(B_3371, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_3376, k3_orders_2(A_3374, B_3371, C_3375)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_3375, u1_struct_0(A_3374)) | ~m1_subset_1(B_3371, k1_zfmisc_1(u1_struct_0(A_3374))) | ~l1_orders_2(A_3374) | ~v5_orders_2(A_3374) | ~v4_orders_2(A_3374) | ~v3_orders_2(A_3374) | v2_struct_0(A_3374) | k3_orders_2(A_3374, B_3371, C_3375)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3374, B_3371, C_3375), k1_zfmisc_1(A_3376)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_43077])).
% 26.82/17.04  tff(c_43675, plain, (![A_3439, A_3440, B_3441, C_3442]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3439, k3_orders_2(A_3440, B_3441, C_3442))) | ~m2_orders_2(B_3441, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_3439, k3_orders_2(A_3440, B_3441, C_3442)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_3442, u1_struct_0(A_3440)) | ~m1_subset_1(B_3441, k1_zfmisc_1(u1_struct_0(A_3440))) | ~l1_orders_2(A_3440) | ~v5_orders_2(A_3440) | ~v4_orders_2(A_3440) | ~v3_orders_2(A_3440) | v2_struct_0(A_3440) | k3_orders_2(A_3440, B_3441, C_3442)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3440, B_3441, C_3442), k1_zfmisc_1(A_3439)))), inference(negUnitSimplification, [status(thm)], [c_54, c_43083])).
% 26.82/17.04  tff(c_43687, plain, (![A_1, B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_39158, c_43675])).
% 26.82/17.04  tff(c_43705, plain, (![A_1, B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_43687])).
% 26.82/17.04  tff(c_43712, plain, (![A_3443, B_3444, C_3445]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3443, k3_orders_2('#skF_2', B_3444, C_3445))) | ~m2_orders_2(B_3444, '#skF_2', '#skF_4') | ~m1_subset_1(C_3445, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3444, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3444, C_3445)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3444, C_3445), k1_zfmisc_1(A_3443)))), inference(negUnitSimplification, [status(thm)], [c_54, c_43705])).
% 26.82/17.04  tff(c_43714, plain, (![A_3443, B_3444, C_3445]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3443, k3_orders_2('#skF_2', B_3444, C_3445))) | ~m1_subset_1('#skF_1'(A_3443, k3_orders_2('#skF_2', B_3444, C_3445)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_3444, '#skF_2', '#skF_4') | ~m1_subset_1(C_3445, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3444, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3444, C_3445)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3444, C_3445), k1_zfmisc_1(A_3443)))), inference(resolution, [status(thm)], [c_43712, c_22])).
% 26.82/17.04  tff(c_43720, plain, (![A_3443, B_3444, C_3445]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3443, k3_orders_2('#skF_2', B_3444, C_3445))) | ~m1_subset_1('#skF_1'(A_3443, k3_orders_2('#skF_2', B_3444, C_3445)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_3444, '#skF_2', '#skF_4') | ~m1_subset_1(C_3445, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3444, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3444, C_3445)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3444, C_3445), k1_zfmisc_1(A_3443)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_43714])).
% 26.82/17.04  tff(c_43722, plain, (![A_3446, B_3447, C_3448]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3446, k3_orders_2('#skF_2', B_3447, C_3448))) | ~m1_subset_1('#skF_1'(A_3446, k3_orders_2('#skF_2', B_3447, C_3448)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_3447, '#skF_2', '#skF_4') | ~m1_subset_1(C_3448, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3447, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3447, C_3448)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3447, C_3448), k1_zfmisc_1(A_3446)))), inference(negUnitSimplification, [status(thm)], [c_54, c_43720])).
% 26.82/17.04  tff(c_43734, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_39158, c_43722])).
% 26.82/17.04  tff(c_43755, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_43734])).
% 26.82/17.04  tff(c_43759, plain, (![A_3449, B_3450, C_3451]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3449, k3_orders_2('#skF_2', B_3450, C_3451))) | ~m2_orders_2(B_3450, '#skF_2', '#skF_4') | ~m1_subset_1(C_3451, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3450, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3450, C_3451)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3450, C_3451), k1_zfmisc_1(A_3449)))), inference(negUnitSimplification, [status(thm)], [c_54, c_43755])).
% 26.82/17.04  tff(c_1450, plain, (![A_349, A_350, B_351, C_352]: (r2_orders_2(A_349, '#skF_1'(A_350, k3_orders_2(A_349, B_351, C_352)), C_352) | ~m1_subset_1(C_352, u1_struct_0(A_349)) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_orders_2(A_349) | ~v5_orders_2(A_349) | ~v4_orders_2(A_349) | ~v3_orders_2(A_349) | v2_struct_0(A_349) | k3_orders_2(A_349, B_351, C_352)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_349, B_351, C_352), k1_zfmisc_1(A_350)))), inference(resolution, [status(thm)], [c_294, c_914])).
% 26.82/17.04  tff(c_1472, plain, (![A_349, A_350, B_351, C_352]: (r1_orders_2(A_349, '#skF_1'(A_350, k3_orders_2(A_349, B_351, C_352)), C_352) | ~m1_subset_1('#skF_1'(A_350, k3_orders_2(A_349, B_351, C_352)), u1_struct_0(A_349)) | ~m1_subset_1(C_352, u1_struct_0(A_349)) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_orders_2(A_349) | ~v5_orders_2(A_349) | ~v4_orders_2(A_349) | ~v3_orders_2(A_349) | v2_struct_0(A_349) | k3_orders_2(A_349, B_351, C_352)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_349, B_351, C_352), k1_zfmisc_1(A_350)))), inference(resolution, [status(thm)], [c_1450, c_12])).
% 26.82/17.04  tff(c_40014, plain, (![A_3119, A_3120, B_3121, C_3122]: (r1_orders_2(A_3119, '#skF_1'(A_3120, k3_orders_2(A_3119, B_3121, C_3122)), C_3122) | ~m1_subset_1('#skF_1'(A_3120, k3_orders_2(A_3119, B_3121, C_3122)), u1_struct_0(A_3119)) | ~m1_subset_1(C_3122, u1_struct_0(A_3119)) | ~m1_subset_1(B_3121, k1_zfmisc_1(u1_struct_0(A_3119))) | ~l1_orders_2(A_3119) | ~v5_orders_2(A_3119) | ~v4_orders_2(A_3119) | ~v3_orders_2(A_3119) | v2_struct_0(A_3119) | k3_orders_2(A_3119, B_3121, C_3122)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3119, B_3121, C_3122), k1_zfmisc_1(A_3120)))), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_1472])).
% 26.82/17.04  tff(c_40025, plain, (![A_3120, B_3121, C_3122]: (r1_orders_2('#skF_2', '#skF_1'(A_3120, k3_orders_2('#skF_2', B_3121, C_3122)), C_3122) | ~m1_subset_1(C_3122, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3121, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_3121, C_3122)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3121, C_3122), k1_zfmisc_1(A_3120)) | ~r2_hidden('#skF_1'(A_3120, k3_orders_2('#skF_2', B_3121, C_3122)), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_40014])).
% 26.82/17.04  tff(c_40033, plain, (![A_3120, B_3121, C_3122]: (r1_orders_2('#skF_2', '#skF_1'(A_3120, k3_orders_2('#skF_2', B_3121, C_3122)), C_3122) | ~m1_subset_1(C_3122, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3121, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_3121, C_3122)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3121, C_3122), k1_zfmisc_1(A_3120)) | ~r2_hidden('#skF_1'(A_3120, k3_orders_2('#skF_2', B_3121, C_3122)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_40025])).
% 26.82/17.04  tff(c_40052, plain, (![A_3126, B_3127, C_3128]: (r1_orders_2('#skF_2', '#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, C_3128)), C_3128) | ~m1_subset_1(C_3128, u1_struct_0('#skF_2')) | ~m1_subset_1(B_3127, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3127, C_3128)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3127, C_3128), k1_zfmisc_1(A_3126)) | ~r2_hidden('#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, C_3128)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_40033])).
% 26.82/17.04  tff(c_40073, plain, (![A_3126, B_3127]: ('#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_3127, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3127, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3127, '#skF_3'), k1_zfmisc_1(A_3126)) | ~r2_hidden('#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3')), '#skF_5'))), inference(resolution, [status(thm)], [c_40052, c_411])).
% 26.82/17.04  tff(c_40098, plain, (![A_3126, B_3127]: ('#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3'))) | ~m1_subset_1(B_3127, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3127, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3127, '#skF_3'), k1_zfmisc_1(A_3126)) | ~r2_hidden('#skF_1'(A_3126, k3_orders_2('#skF_2', B_3127, '#skF_3')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40073])).
% 26.82/17.04  tff(c_43781, plain, (![A_3449, B_3450]: ('#skF_1'(A_3449, k3_orders_2('#skF_2', B_3450, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(A_3449, k3_orders_2('#skF_2', B_3450, '#skF_3')), '#skF_5') | ~m2_orders_2(B_3450, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_3450, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3450, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3450, '#skF_3'), k1_zfmisc_1(A_3449)))), inference(resolution, [status(thm)], [c_43759, c_40098])).
% 26.82/17.04  tff(c_43858, plain, (![A_3452, B_3453]: ('#skF_1'(A_3452, k3_orders_2('#skF_2', B_3453, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(A_3452, k3_orders_2('#skF_2', B_3453, '#skF_3')), '#skF_5') | ~m2_orders_2(B_3453, '#skF_2', '#skF_4') | ~m1_subset_1(B_3453, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3453, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3453, '#skF_3'), k1_zfmisc_1(A_3452)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_43781])).
% 26.82/17.04  tff(c_43862, plain, (![A_1]: ('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_39130, c_43858])).
% 26.82/17.04  tff(c_43873, plain, (![A_1]: ('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_40, c_43862])).
% 26.82/17.04  tff(c_43954, plain, (![A_3460]: ('#skF_1'(A_3460, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_3460)))), inference(negUnitSimplification, [status(thm)], [c_39173, c_54, c_43873])).
% 26.82/17.04  tff(c_43958, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_43954])).
% 26.82/17.04  tff(c_43961, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_43958])).
% 26.82/17.04  tff(c_43962, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_54, c_43961])).
% 26.82/17.04  tff(c_43756, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_54, c_43755])).
% 26.82/17.04  tff(c_43969, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_43962, c_43756])).
% 26.82/17.04  tff(c_44180, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_44, c_40, c_43969])).
% 26.82/17.04  tff(c_44181, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_39173, c_123, c_44180])).
% 26.82/17.04  tff(c_44359, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_44181])).
% 26.82/17.04  tff(c_44362, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_44359])).
% 26.82/17.04  tff(c_44364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_44362])).
% 26.82/17.04  tff(c_44366, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_39072])).
% 26.82/17.04  tff(c_1242, plain, (![A_323, B_324]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_323, B_324)) | ~m2_orders_2(B_324, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_323, B_324), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(A_323)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1225])).
% 26.82/17.04  tff(c_1261, plain, (![A_323, B_324]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_323, B_324)) | ~m2_orders_2(B_324, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_323, B_324), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(A_323)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_1242])).
% 26.82/17.04  tff(c_1262, plain, (![A_323, B_324]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_323, B_324)) | ~m2_orders_2(B_324, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_323, B_324), u1_struct_0('#skF_2')) | k1_xboole_0=B_324 | ~m1_subset_1(B_324, k1_zfmisc_1(A_323)))), inference(negUnitSimplification, [status(thm)], [c_54, c_1261])).
% 26.82/17.04  tff(c_44423, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44366, c_1262])).
% 26.82/17.04  tff(c_44448, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_40, c_44423])).
% 26.82/17.04  tff(c_44464, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_44448])).
% 26.82/17.04  tff(c_44555, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_36])).
% 26.82/17.05  tff(c_44512, plain, (![A_1, A_152, B_153, C_154]: (r2_hidden('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), B_153) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_717])).
% 26.82/17.05  tff(c_44540, plain, (![A_1, A_152, B_153, C_154]: (m1_subset_1('#skF_1'(A_1, k3_orders_2(A_152, B_153, C_154)), u1_struct_0(A_152)) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152) | k3_orders_2(A_152, B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2(A_152, B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_294])).
% 26.82/17.05  tff(c_49336, plain, (![C_3819, A_3818, D_3816, B_3815, A_3820, A_3817]: (r3_orders_2(A_3817, k1_funct_1(D_3816, u1_struct_0(A_3817)), '#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819))) | ~m2_orders_2(B_3815, A_3817, D_3816) | ~m1_orders_1(D_3816, k1_orders_1(u1_struct_0(A_3817))) | ~m1_subset_1(k1_funct_1(D_3816, u1_struct_0(A_3817)), u1_struct_0(A_3817)) | ~m1_subset_1('#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819)), u1_struct_0(A_3817)) | ~l1_orders_2(A_3817) | ~v5_orders_2(A_3817) | ~v4_orders_2(A_3817) | ~v3_orders_2(A_3817) | v2_struct_0(A_3817) | ~m1_subset_1(C_3819, u1_struct_0(A_3818)) | ~m1_subset_1(B_3815, k1_zfmisc_1(u1_struct_0(A_3818))) | ~l1_orders_2(A_3818) | ~v5_orders_2(A_3818) | ~v4_orders_2(A_3818) | ~v3_orders_2(A_3818) | v2_struct_0(A_3818) | k3_orders_2(A_3818, B_3815, C_3819)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3818, B_3815, C_3819), k1_zfmisc_1(A_3820)))), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_1406])).
% 26.82/17.05  tff(c_49344, plain, (![A_3820, A_3818, B_3815, C_3819]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819))) | ~m2_orders_2(B_3815, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_3819, u1_struct_0(A_3818)) | ~m1_subset_1(B_3815, k1_zfmisc_1(u1_struct_0(A_3818))) | ~l1_orders_2(A_3818) | ~v5_orders_2(A_3818) | ~v4_orders_2(A_3818) | ~v3_orders_2(A_3818) | v2_struct_0(A_3818) | k3_orders_2(A_3818, B_3815, C_3819)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3818, B_3815, C_3819), k1_zfmisc_1(A_3820)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_49336])).
% 26.82/17.05  tff(c_49350, plain, (![A_3820, A_3818, B_3815, C_3819]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819))) | ~m2_orders_2(B_3815, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_3820, k3_orders_2(A_3818, B_3815, C_3819)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_3819, u1_struct_0(A_3818)) | ~m1_subset_1(B_3815, k1_zfmisc_1(u1_struct_0(A_3818))) | ~l1_orders_2(A_3818) | ~v5_orders_2(A_3818) | ~v4_orders_2(A_3818) | ~v3_orders_2(A_3818) | v2_struct_0(A_3818) | k3_orders_2(A_3818, B_3815, C_3819)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3818, B_3815, C_3819), k1_zfmisc_1(A_3820)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_49344])).
% 26.82/17.05  tff(c_52644, plain, (![A_4047, A_4048, B_4049, C_4050]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4047, k3_orders_2(A_4048, B_4049, C_4050))) | ~m2_orders_2(B_4049, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_4047, k3_orders_2(A_4048, B_4049, C_4050)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_4050, u1_struct_0(A_4048)) | ~m1_subset_1(B_4049, k1_zfmisc_1(u1_struct_0(A_4048))) | ~l1_orders_2(A_4048) | ~v5_orders_2(A_4048) | ~v4_orders_2(A_4048) | ~v3_orders_2(A_4048) | v2_struct_0(A_4048) | k3_orders_2(A_4048, B_4049, C_4050)='#skF_5' | ~m1_subset_1(k3_orders_2(A_4048, B_4049, C_4050), k1_zfmisc_1(A_4047)))), inference(negUnitSimplification, [status(thm)], [c_54, c_49350])).
% 26.82/17.05  tff(c_52659, plain, (![A_1, B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_44540, c_52644])).
% 26.82/17.05  tff(c_52684, plain, (![A_1, B_153, C_154]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_52659])).
% 26.82/17.05  tff(c_52692, plain, (![A_4051, B_4052, C_4053]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4051, k3_orders_2('#skF_2', B_4052, C_4053))) | ~m2_orders_2(B_4052, '#skF_2', '#skF_4') | ~m1_subset_1(C_4053, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4052, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4052, C_4053)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4052, C_4053), k1_zfmisc_1(A_4051)))), inference(negUnitSimplification, [status(thm)], [c_54, c_52684])).
% 26.82/17.05  tff(c_52694, plain, (![A_4051, B_4052, C_4053]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4051, k3_orders_2('#skF_2', B_4052, C_4053))) | ~m1_subset_1('#skF_1'(A_4051, k3_orders_2('#skF_2', B_4052, C_4053)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_4052, '#skF_2', '#skF_4') | ~m1_subset_1(C_4053, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4052, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4052, C_4053)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4052, C_4053), k1_zfmisc_1(A_4051)))), inference(resolution, [status(thm)], [c_52692, c_22])).
% 26.82/17.05  tff(c_52703, plain, (![A_4051, B_4052, C_4053]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4051, k3_orders_2('#skF_2', B_4052, C_4053))) | ~m1_subset_1('#skF_1'(A_4051, k3_orders_2('#skF_2', B_4052, C_4053)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_4052, '#skF_2', '#skF_4') | ~m1_subset_1(C_4053, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4052, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4052, C_4053)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4052, C_4053), k1_zfmisc_1(A_4051)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_52694])).
% 26.82/17.05  tff(c_52705, plain, (![A_4054, B_4055, C_4056]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4054, k3_orders_2('#skF_2', B_4055, C_4056))) | ~m1_subset_1('#skF_1'(A_4054, k3_orders_2('#skF_2', B_4055, C_4056)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_4055, '#skF_2', '#skF_4') | ~m1_subset_1(C_4056, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4055, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4055, C_4056)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4055, C_4056), k1_zfmisc_1(A_4054)))), inference(negUnitSimplification, [status(thm)], [c_54, c_52703])).
% 26.82/17.05  tff(c_52720, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_44540, c_52705])).
% 26.82/17.05  tff(c_52745, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_52720])).
% 26.82/17.05  tff(c_52753, plain, (![A_4057, B_4058, C_4059]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_4057, k3_orders_2('#skF_2', B_4058, C_4059))) | ~m2_orders_2(B_4058, '#skF_2', '#skF_4') | ~m1_subset_1(C_4059, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4058, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4058, C_4059)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4058, C_4059), k1_zfmisc_1(A_4057)))), inference(negUnitSimplification, [status(thm)], [c_54, c_52745])).
% 26.82/17.05  tff(c_46205, plain, (![A_3653, A_3654, B_3655, C_3656]: (m1_subset_1('#skF_1'(A_3653, k3_orders_2(A_3654, B_3655, C_3656)), u1_struct_0(A_3654)) | ~m1_subset_1(C_3656, u1_struct_0(A_3654)) | ~m1_subset_1(B_3655, k1_zfmisc_1(u1_struct_0(A_3654))) | ~l1_orders_2(A_3654) | ~v5_orders_2(A_3654) | ~v4_orders_2(A_3654) | ~v3_orders_2(A_3654) | v2_struct_0(A_3654) | k3_orders_2(A_3654, B_3655, C_3656)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3654, B_3655, C_3656), k1_zfmisc_1(A_3653)))), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_294])).
% 26.82/17.05  tff(c_45297, plain, (![A_349, A_350, B_351, C_352]: (r1_orders_2(A_349, '#skF_1'(A_350, k3_orders_2(A_349, B_351, C_352)), C_352) | ~m1_subset_1('#skF_1'(A_350, k3_orders_2(A_349, B_351, C_352)), u1_struct_0(A_349)) | ~m1_subset_1(C_352, u1_struct_0(A_349)) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_orders_2(A_349) | ~v5_orders_2(A_349) | ~v4_orders_2(A_349) | ~v3_orders_2(A_349) | v2_struct_0(A_349) | k3_orders_2(A_349, B_351, C_352)='#skF_5' | ~m1_subset_1(k3_orders_2(A_349, B_351, C_352), k1_zfmisc_1(A_350)))), inference(demodulation, [status(thm), theory('equality')], [c_44464, c_1472])).
% 26.82/17.05  tff(c_46455, plain, (![A_3675, A_3676, B_3677, C_3678]: (r1_orders_2(A_3675, '#skF_1'(A_3676, k3_orders_2(A_3675, B_3677, C_3678)), C_3678) | ~m1_subset_1(C_3678, u1_struct_0(A_3675)) | ~m1_subset_1(B_3677, k1_zfmisc_1(u1_struct_0(A_3675))) | ~l1_orders_2(A_3675) | ~v5_orders_2(A_3675) | ~v4_orders_2(A_3675) | ~v3_orders_2(A_3675) | v2_struct_0(A_3675) | k3_orders_2(A_3675, B_3677, C_3678)='#skF_5' | ~m1_subset_1(k3_orders_2(A_3675, B_3677, C_3678), k1_zfmisc_1(A_3676)))), inference(resolution, [status(thm)], [c_46205, c_45297])).
% 26.82/17.05  tff(c_46504, plain, (![A_3676, B_3677]: ('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))) | ~r2_hidden('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_3677, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_3677, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3677, '#skF_3'), k1_zfmisc_1(A_3676)))), inference(resolution, [status(thm)], [c_46455, c_411])).
% 26.82/17.05  tff(c_46565, plain, (![A_3676, B_3677]: ('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))) | ~r2_hidden('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3')), '#skF_5') | ~m1_subset_1(B_3677, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_3677, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3677, '#skF_3'), k1_zfmisc_1(A_3676)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_46504])).
% 26.82/17.05  tff(c_46566, plain, (![A_3676, B_3677]: ('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3'))) | ~r2_hidden('#skF_1'(A_3676, k3_orders_2('#skF_2', B_3677, '#skF_3')), '#skF_5') | ~m1_subset_1(B_3677, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_3677, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_3677, '#skF_3'), k1_zfmisc_1(A_3676)))), inference(negUnitSimplification, [status(thm)], [c_54, c_46565])).
% 26.82/17.05  tff(c_52783, plain, (![A_4057, B_4058]: ('#skF_1'(A_4057, k3_orders_2('#skF_2', B_4058, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(A_4057, k3_orders_2('#skF_2', B_4058, '#skF_3')), '#skF_5') | ~m2_orders_2(B_4058, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_4058, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4058, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4058, '#skF_3'), k1_zfmisc_1(A_4057)))), inference(resolution, [status(thm)], [c_52753, c_46566])).
% 26.82/17.05  tff(c_52882, plain, (![A_4060, B_4061]: ('#skF_1'(A_4060, k3_orders_2('#skF_2', B_4061, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(A_4060, k3_orders_2('#skF_2', B_4061, '#skF_3')), '#skF_5') | ~m2_orders_2(B_4061, '#skF_2', '#skF_4') | ~m1_subset_1(B_4061, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4061, '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_4061, '#skF_3'), k1_zfmisc_1(A_4060)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52783])).
% 26.82/17.05  tff(c_52890, plain, (![A_1]: ('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_44512, c_52882])).
% 26.82/17.05  tff(c_52904, plain, (![A_1]: ('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_40, c_52890])).
% 26.82/17.05  tff(c_52921, plain, (![A_4066]: ('#skF_1'(A_4066, k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(A_4066)))), inference(negUnitSimplification, [status(thm)], [c_44555, c_54, c_52904])).
% 26.82/17.05  tff(c_52925, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_52921])).
% 26.82/17.05  tff(c_52928, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_52925])).
% 26.82/17.05  tff(c_52929, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_54, c_52928])).
% 26.82/17.05  tff(c_52746, plain, (![A_1, B_153, C_154]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1, k3_orders_2('#skF_2', B_153, C_154))) | ~m2_orders_2(B_153, '#skF_2', '#skF_4') | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_153, C_154)='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', B_153, C_154), k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_54, c_52745])).
% 26.82/17.05  tff(c_52936, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_52929, c_52746])).
% 26.82/17.05  tff(c_53187, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')='#skF_5' | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_44, c_40, c_52936])).
% 26.82/17.05  tff(c_53188, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44555, c_123, c_53187])).
% 26.82/17.05  tff(c_53408, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_53188])).
% 26.82/17.05  tff(c_53411, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_53408])).
% 26.82/17.05  tff(c_53413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_53411])).
% 26.82/17.05  tff(c_53415, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_44448])).
% 26.82/17.05  tff(c_667, plain, (![A_255, D_256, A_257, B_258]: (r1_orders_2(A_255, k1_funct_1(D_256, u1_struct_0(A_255)), '#skF_1'(A_257, B_258)) | ~m2_orders_2(B_258, A_255, D_256) | ~m1_orders_1(D_256, k1_orders_1(u1_struct_0(A_255))) | ~m1_subset_1(k1_funct_1(D_256, u1_struct_0(A_255)), u1_struct_0(A_255)) | ~m1_subset_1('#skF_1'(A_257, B_258), u1_struct_0(A_255)) | ~l1_orders_2(A_255) | ~v5_orders_2(A_255) | ~v4_orders_2(A_255) | ~v3_orders_2(A_255) | v2_struct_0(A_255) | k1_xboole_0=B_258 | ~m1_subset_1(B_258, k1_zfmisc_1(A_257)))), inference(resolution, [status(thm)], [c_661, c_22])).
% 26.82/17.05  tff(c_167, plain, (![B_11, A_130]: (r2_orders_2('#skF_2', B_11, A_130) | B_11=A_130 | ~r1_orders_2('#skF_2', B_11, A_130) | ~m1_subset_1(B_11, u1_struct_0('#skF_2')) | ~r2_hidden(A_130, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_158])).
% 26.82/17.05  tff(c_53949, plain, (![A_4084]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4084) | A_4084='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4084) | ~r2_hidden(A_4084, '#skF_5'))), inference(resolution, [status(thm)], [c_44366, c_167])).
% 26.82/17.05  tff(c_24, plain, (![A_24, C_36, D_38, B_32]: (~r2_orders_2(A_24, C_36, D_38) | ~r1_orders_2(A_24, B_32, C_36) | r2_orders_2(A_24, B_32, D_38) | ~m1_subset_1(D_38, u1_struct_0(A_24)) | ~m1_subset_1(C_36, u1_struct_0(A_24)) | ~m1_subset_1(B_32, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24) | ~v4_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_135])).
% 26.82/17.05  tff(c_53973, plain, (![B_32, A_4084]: (~r1_orders_2('#skF_2', B_32, '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')) | r2_orders_2('#skF_2', B_32, A_4084) | ~m1_subset_1(A_4084, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_32, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_4084='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4084) | ~r2_hidden(A_4084, '#skF_5'))), inference(resolution, [status(thm)], [c_53949, c_24])).
% 26.82/17.05  tff(c_55180, plain, (![B_4130, A_4131]: (~r1_orders_2('#skF_2', B_4130, '#skF_1'(u1_struct_0('#skF_2'), '#skF_5')) | r2_orders_2('#skF_2', B_4130, A_4131) | ~m1_subset_1(A_4131, u1_struct_0('#skF_2')) | ~m1_subset_1(B_4130, u1_struct_0('#skF_2')) | A_4131='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4131) | ~r2_hidden(A_4131, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44366, c_53973])).
% 26.82/17.05  tff(c_55210, plain, (![D_256, A_4131]: (r2_orders_2('#skF_2', k1_funct_1(D_256, u1_struct_0('#skF_2')), A_4131) | ~m1_subset_1(A_4131, u1_struct_0('#skF_2')) | A_4131='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4131) | ~r2_hidden(A_4131, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_256) | ~m1_orders_1(D_256, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_256, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_667, c_55180])).
% 26.82/17.05  tff(c_55252, plain, (![D_256, A_4131]: (r2_orders_2('#skF_2', k1_funct_1(D_256, u1_struct_0('#skF_2')), A_4131) | ~m1_subset_1(A_4131, u1_struct_0('#skF_2')) | A_4131='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4131) | ~r2_hidden(A_4131, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_256) | ~m1_orders_1(D_256, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_256, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_52, c_50, c_48, c_46, c_44366, c_55210])).
% 26.82/17.05  tff(c_55266, plain, (![D_4132, A_4133]: (r2_orders_2('#skF_2', k1_funct_1(D_4132, u1_struct_0('#skF_2')), A_4133) | ~m1_subset_1(A_4133, u1_struct_0('#skF_2')) | A_4133='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4133) | ~r2_hidden(A_4133, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_4132) | ~m1_orders_1(D_4132, k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1(D_4132, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53415, c_54, c_55252])).
% 26.82/17.05  tff(c_55323, plain, (![D_4135, A_4136]: (r2_orders_2('#skF_2', k1_funct_1(D_4135, u1_struct_0('#skF_2')), A_4136) | ~m1_subset_1(A_4136, u1_struct_0('#skF_2')) | A_4136='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4136) | ~r2_hidden(A_4136, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_4135) | ~m1_orders_1(D_4135, k1_orders_1(u1_struct_0('#skF_2'))) | ~r2_hidden(k1_funct_1(D_4135, u1_struct_0('#skF_2')), '#skF_5'))), inference(resolution, [status(thm)], [c_147, c_55266])).
% 26.82/17.05  tff(c_55342, plain, (![D_4135, A_4136]: (r1_orders_2('#skF_2', k1_funct_1(D_4135, u1_struct_0('#skF_2')), A_4136) | ~m1_subset_1(k1_funct_1(D_4135, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~m1_subset_1(A_4136, u1_struct_0('#skF_2')) | A_4136='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4136) | ~r2_hidden(A_4136, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_4135) | ~m1_orders_1(D_4135, k1_orders_1(u1_struct_0('#skF_2'))) | ~r2_hidden(k1_funct_1(D_4135, u1_struct_0('#skF_2')), '#skF_5'))), inference(resolution, [status(thm)], [c_55323, c_12])).
% 26.82/17.05  tff(c_56654, plain, (![D_4206, A_4207]: (r1_orders_2('#skF_2', k1_funct_1(D_4206, u1_struct_0('#skF_2')), A_4207) | ~m1_subset_1(k1_funct_1(D_4206, u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1(A_4207, u1_struct_0('#skF_2')) | A_4207='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4207) | ~r2_hidden(A_4207, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', D_4206) | ~m1_orders_1(D_4206, k1_orders_1(u1_struct_0('#skF_2'))) | ~r2_hidden(k1_funct_1(D_4206, u1_struct_0('#skF_2')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55342])).
% 26.82/17.05  tff(c_56659, plain, (![A_4207]: (r1_orders_2('#skF_2', k1_funct_1('#skF_4', u1_struct_0('#skF_2')), A_4207) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(A_4207, u1_struct_0('#skF_2')) | A_4207='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4207) | ~r2_hidden(A_4207, '#skF_5') | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~r2_hidden(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_56654])).
% 26.82/17.05  tff(c_56662, plain, (![A_4207]: (r1_orders_2('#skF_2', '#skF_3', A_4207) | ~m1_subset_1(A_4207, u1_struct_0('#skF_2')) | A_4207='#skF_1'(u1_struct_0('#skF_2'), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), '#skF_5'), A_4207) | ~r2_hidden(A_4207, '#skF_5') | ~r2_hidden('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_40, c_44, c_38, c_56659])).
% 26.82/17.05  tff(c_56663, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_56662])).
% 26.82/17.05  tff(c_56978, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_56964])).
% 26.82/17.05  tff(c_57114, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_56978, c_717])).
% 26.82/17.05  tff(c_57339, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_144, c_44, c_57114])).
% 26.82/17.05  tff(c_57340, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_54, c_56663, c_57339])).
% 26.82/17.05  tff(c_57530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56979, c_57340])).
% 26.82/17.05  tff(c_57532, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_56662])).
% 26.82/17.05  tff(c_57579, plain, (![A_4226, D_4227]: (r3_orders_2(A_4226, k1_funct_1(D_4227, u1_struct_0(A_4226)), '#skF_3') | ~m2_orders_2('#skF_5', A_4226, D_4227) | ~m1_orders_1(D_4227, k1_orders_1(u1_struct_0(A_4226))) | ~m1_subset_1(k1_funct_1(D_4227, u1_struct_0(A_4226)), u1_struct_0(A_4226)) | ~m1_subset_1('#skF_3', u1_struct_0(A_4226)) | ~l1_orders_2(A_4226) | ~v5_orders_2(A_4226) | ~v4_orders_2(A_4226) | ~v3_orders_2(A_4226) | v2_struct_0(A_4226))), inference(resolution, [status(thm)], [c_57532, c_34])).
% 26.82/17.05  tff(c_57586, plain, (r3_orders_2('#skF_2', k1_funct_1('#skF_4', u1_struct_0('#skF_2')), '#skF_3') | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_57579])).
% 26.82/17.05  tff(c_57592, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_44, c_42, c_40, c_38, c_57586])).
% 26.82/17.05  tff(c_57593, plain, (r3_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_57592])).
% 26.82/17.05  tff(c_57595, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_57593, c_22])).
% 26.82/17.05  tff(c_57598, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_57595])).
% 26.82/17.05  tff(c_57600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_123, c_57598])).
% 26.82/17.05  tff(c_57602, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_122])).
% 26.82/17.05  tff(c_57995, plain, (![A_4300, B_4301, B_4302]: (r2_orders_2(A_4300, B_4301, '#skF_1'(u1_struct_0(A_4300), B_4302)) | B_4301='#skF_1'(u1_struct_0(A_4300), B_4302) | ~r1_orders_2(A_4300, B_4301, '#skF_1'(u1_struct_0(A_4300), B_4302)) | ~m1_subset_1(B_4301, u1_struct_0(A_4300)) | ~l1_orders_2(A_4300) | k1_xboole_0=B_4302 | ~m1_subset_1(B_4302, k1_zfmisc_1(u1_struct_0(A_4300))))), inference(resolution, [status(thm)], [c_4, c_74])).
% 26.82/17.05  tff(c_58988, plain, (![A_4446, B_4447, B_4448, B_4449]: (~r1_orders_2(A_4446, B_4447, B_4448) | r2_orders_2(A_4446, B_4447, '#skF_1'(u1_struct_0(A_4446), B_4449)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_4446), B_4449), u1_struct_0(A_4446)) | ~m1_subset_1(B_4447, u1_struct_0(A_4446)) | ~v5_orders_2(A_4446) | ~v4_orders_2(A_4446) | B_4448='#skF_1'(u1_struct_0(A_4446), B_4449) | ~r1_orders_2(A_4446, B_4448, '#skF_1'(u1_struct_0(A_4446), B_4449)) | ~m1_subset_1(B_4448, u1_struct_0(A_4446)) | ~l1_orders_2(A_4446) | k1_xboole_0=B_4449 | ~m1_subset_1(B_4449, k1_zfmisc_1(u1_struct_0(A_4446))))), inference(resolution, [status(thm)], [c_57995, c_24])).
% 26.82/17.05  tff(c_59002, plain, (![B_4449]: (r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4449)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4449), u1_struct_0('#skF_2')) | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | '#skF_1'(u1_struct_0('#skF_2'), B_4449)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4449)) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | k1_xboole_0=B_4449 | ~m1_subset_1(B_4449, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_57602, c_58988])).
% 26.82/17.05  tff(c_59031, plain, (![B_4452]: (r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4452)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4452), u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_4452)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4452)) | k1_xboole_0=B_4452 | ~m1_subset_1(B_4452, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_50, c_48, c_59002])).
% 26.82/17.05  tff(c_59054, plain, (![B_4453]: (r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4453)) | '#skF_1'(u1_struct_0('#skF_2'), B_4453)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4453)) | k1_xboole_0=B_4453 | ~m1_subset_1(B_4453, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_59031])).
% 26.82/17.05  tff(c_59056, plain, (![B_32, B_4453]: (~r1_orders_2('#skF_2', B_32, '#skF_3') | r2_orders_2('#skF_2', B_32, '#skF_1'(u1_struct_0('#skF_2'), B_4453)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4453), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_32, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | '#skF_1'(u1_struct_0('#skF_2'), B_4453)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4453)) | k1_xboole_0=B_4453 | ~m1_subset_1(B_4453, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_59054, c_24])).
% 26.82/17.05  tff(c_59132, plain, (![B_4469, B_4470]: (~r1_orders_2('#skF_2', B_4469, '#skF_3') | r2_orders_2('#skF_2', B_4469, '#skF_1'(u1_struct_0('#skF_2'), B_4470)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4470), u1_struct_0('#skF_2')) | ~m1_subset_1(B_4469, u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_4470)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4470)) | k1_xboole_0=B_4470 | ~m1_subset_1(B_4470, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_59056])).
% 26.82/17.05  tff(c_59152, plain, (![B_4471, B_4472]: (~r1_orders_2('#skF_2', B_4471, '#skF_3') | r2_orders_2('#skF_2', B_4471, '#skF_1'(u1_struct_0('#skF_2'), B_4472)) | ~m1_subset_1(B_4471, u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_4472)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4472)) | k1_xboole_0=B_4472 | ~m1_subset_1(B_4472, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_59132])).
% 26.82/17.05  tff(c_59159, plain, (![B_4472]: (~l1_orders_2('#skF_2') | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_4472), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4472), u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_4472)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4472)) | k1_xboole_0=B_4472 | ~m1_subset_1(B_4472, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_59152, c_10])).
% 26.82/17.05  tff(c_59169, plain, (![B_4473]: (~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_4473), '#skF_3') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_4473), u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_4473)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_4473)) | k1_xboole_0=B_4473 | ~m1_subset_1(B_4473, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_59159])).
% 26.82/17.05  tff(c_59191, plain, (![B_2]: (~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_2)) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_59169])).
% 26.82/17.05  tff(c_59699, plain, (![B_4517]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_4517, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4517, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4517, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_59685, c_59191])).
% 26.82/17.05  tff(c_59747, plain, (![B_4517]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))) | ~m1_subset_1(B_4517, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_4517, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4517, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_59699])).
% 26.82/17.05  tff(c_59748, plain, (![B_4517]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_4517, '#skF_3'))) | ~m1_subset_1(B_4517, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_4517, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_4517, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_59747])).
% 26.82/17.05  tff(c_76162, plain, (![B_5633]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5633, '#skF_3'))='#skF_3' | ~m2_orders_2(B_5633, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_5633, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5633, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5633, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_76142, c_59748])).
% 26.82/17.05  tff(c_76243, plain, (![B_5635]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5635, '#skF_3'))='#skF_3' | ~m2_orders_2(B_5635, '#skF_2', '#skF_4') | ~m1_subset_1(B_5635, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_5635, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', B_5635, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76162])).
% 26.82/17.05  tff(c_76247, plain, (![B_15]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_15, '#skF_3'))='#skF_3' | ~m2_orders_2(B_15, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_15, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_76243])).
% 26.82/17.05  tff(c_76250, plain, (![B_15]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_15, '#skF_3'))='#skF_3' | ~m2_orders_2(B_15, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_15, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_76247])).
% 26.82/17.05  tff(c_76252, plain, (![B_5636]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_5636, '#skF_3'))='#skF_3' | ~m2_orders_2(B_5636, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_5636, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_5636, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_76250])).
% 26.82/17.05  tff(c_76271, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_57630, c_76252])).
% 26.82/17.05  tff(c_76285, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76271])).
% 26.82/17.05  tff(c_76286, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_36, c_76285])).
% 26.82/17.05  tff(c_58392, plain, (![A_4257, A_1, B_4258, C_4259]: (r2_orders_2(A_4257, '#skF_1'(A_1, k3_orders_2(A_4257, B_4258, C_4259)), C_4259) | ~m1_subset_1(C_4259, u1_struct_0(A_4257)) | ~m1_subset_1(B_4258, k1_zfmisc_1(u1_struct_0(A_4257))) | ~l1_orders_2(A_4257) | ~v5_orders_2(A_4257) | ~v4_orders_2(A_4257) | ~v3_orders_2(A_4257) | v2_struct_0(A_4257) | k3_orders_2(A_4257, B_4258, C_4259)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_4257, B_4258, C_4259), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_57782, c_58383])).
% 26.82/17.05  tff(c_76406, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_76286, c_58392])).
% 26.82/17.05  tff(c_76642, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_57630, c_44, c_76406])).
% 26.82/17.05  tff(c_76643, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_54, c_58588, c_76642])).
% 26.82/17.05  tff(c_76741, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_76643])).
% 26.82/17.05  tff(c_76744, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_57630, c_44, c_76741])).
% 26.82/17.05  tff(c_76746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_76744])).
% 26.82/17.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.82/17.05  
% 26.82/17.05  Inference rules
% 26.82/17.05  ----------------------
% 26.82/17.05  #Ref     : 0
% 26.82/17.05  #Sup     : 14889
% 26.82/17.05  #Fact    : 0
% 26.82/17.05  #Define  : 0
% 26.82/17.05  #Split   : 55
% 26.82/17.05  #Chain   : 0
% 26.82/17.05  #Close   : 0
% 26.82/17.05  
% 26.82/17.05  Ordering : KBO
% 26.82/17.05  
% 26.82/17.05  Simplification rules
% 26.82/17.05  ----------------------
% 26.82/17.05  #Subsume      : 8366
% 26.82/17.05  #Demod        : 22462
% 26.82/17.05  #Tautology    : 926
% 26.82/17.05  #SimpNegUnit  : 3910
% 26.82/17.05  #BackRed      : 677
% 26.82/17.05  
% 26.82/17.05  #Partial instantiations: 0
% 26.82/17.05  #Strategies tried      : 1
% 26.82/17.05  
% 26.82/17.05  Timing (in seconds)
% 26.82/17.05  ----------------------
% 26.82/17.05  Preprocessing        : 0.37
% 26.82/17.05  Parsing              : 0.22
% 26.82/17.05  CNF conversion       : 0.03
% 26.82/17.05  Main loop            : 15.74
% 26.82/17.05  Inferencing          : 3.64
% 26.82/17.05  Reduction            : 4.47
% 26.82/17.05  Demodulation         : 3.12
% 26.82/17.05  BG Simplification    : 0.31
% 26.82/17.05  Subsumption          : 6.69
% 26.82/17.05  Abstraction          : 0.67
% 26.82/17.05  MUC search           : 0.00
% 26.82/17.05  Cooper               : 0.00
% 26.82/17.05  Total                : 16.23
% 26.82/17.05  Index Insertion      : 0.00
% 26.82/17.05  Index Deletion       : 0.00
% 26.82/17.05  Index Matching       : 0.00
% 26.82/17.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
