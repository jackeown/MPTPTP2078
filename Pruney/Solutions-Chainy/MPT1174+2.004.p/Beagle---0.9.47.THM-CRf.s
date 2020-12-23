%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:52 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 381 expanded)
%              Number of leaves         :   38 ( 169 expanded)
%              Depth                    :   37
%              Number of atoms          :  427 (2052 expanded)
%              Number of equality atoms :   44 ( 275 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_224,negated_conjecture,(
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

tff(f_104,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_84,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_170,axiom,(
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

tff(f_199,axiom,(
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

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_144,axiom,(
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

tff(f_67,axiom,(
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

tff(c_36,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_52,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_48,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_46,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_42,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_40,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_9360,plain,(
    ! [C_1009,A_1010,B_1011] :
      ( m1_subset_1(C_1009,k1_zfmisc_1(u1_struct_0(A_1010)))
      | ~ m2_orders_2(C_1009,A_1010,B_1011)
      | ~ m1_orders_1(B_1011,k1_orders_1(u1_struct_0(A_1010)))
      | ~ l1_orders_2(A_1010)
      | ~ v5_orders_2(A_1010)
      | ~ v4_orders_2(A_1010)
      | ~ v3_orders_2(A_1010)
      | v2_struct_0(A_1010) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9362,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_9360])).

tff(c_9365,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_42,c_9362])).

tff(c_9366,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9365])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9390,plain,(
    ! [A_1013,B_1014,C_1015] :
      ( m1_subset_1(k3_orders_2(A_1013,B_1014,C_1015),k1_zfmisc_1(u1_struct_0(A_1013)))
      | ~ m1_subset_1(C_1015,u1_struct_0(A_1013))
      | ~ m1_subset_1(B_1014,k1_zfmisc_1(u1_struct_0(A_1013)))
      | ~ l1_orders_2(A_1013)
      | ~ v5_orders_2(A_1013)
      | ~ v4_orders_2(A_1013)
      | ~ v3_orders_2(A_1013)
      | v2_struct_0(A_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9484,plain,(
    ! [A_1039,A_1040,B_1041,C_1042] :
      ( m1_subset_1(A_1039,u1_struct_0(A_1040))
      | ~ r2_hidden(A_1039,k3_orders_2(A_1040,B_1041,C_1042))
      | ~ m1_subset_1(C_1042,u1_struct_0(A_1040))
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_orders_2(A_1040)
      | ~ v5_orders_2(A_1040)
      | ~ v4_orders_2(A_1040)
      | ~ v3_orders_2(A_1040)
      | v2_struct_0(A_1040) ) ),
    inference(resolution,[status(thm)],[c_9390,c_2])).

tff(c_9488,plain,(
    ! [A_1040,B_1041,C_1042] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_1040,B_1041,C_1042)),u1_struct_0(A_1040))
      | ~ m1_subset_1(C_1042,u1_struct_0(A_1040))
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_orders_2(A_1040)
      | ~ v5_orders_2(A_1040)
      | ~ v4_orders_2(A_1040)
      | ~ v3_orders_2(A_1040)
      | v2_struct_0(A_1040)
      | k3_orders_2(A_1040,B_1041,C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_9484])).

tff(c_9658,plain,(
    ! [A_1077,B_1078,C_1079,D_1080] :
      ( r2_orders_2(A_1077,B_1078,C_1079)
      | ~ r2_hidden(B_1078,k3_orders_2(A_1077,D_1080,C_1079))
      | ~ m1_subset_1(D_1080,k1_zfmisc_1(u1_struct_0(A_1077)))
      | ~ m1_subset_1(C_1079,u1_struct_0(A_1077))
      | ~ m1_subset_1(B_1078,u1_struct_0(A_1077))
      | ~ l1_orders_2(A_1077)
      | ~ v5_orders_2(A_1077)
      | ~ v4_orders_2(A_1077)
      | ~ v3_orders_2(A_1077)
      | v2_struct_0(A_1077) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_9824,plain,(
    ! [A_1115,D_1116,C_1117] :
      ( r2_orders_2(A_1115,'#skF_1'(k3_orders_2(A_1115,D_1116,C_1117)),C_1117)
      | ~ m1_subset_1(D_1116,k1_zfmisc_1(u1_struct_0(A_1115)))
      | ~ m1_subset_1(C_1117,u1_struct_0(A_1115))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1115,D_1116,C_1117)),u1_struct_0(A_1115))
      | ~ l1_orders_2(A_1115)
      | ~ v5_orders_2(A_1115)
      | ~ v4_orders_2(A_1115)
      | ~ v3_orders_2(A_1115)
      | v2_struct_0(A_1115)
      | k3_orders_2(A_1115,D_1116,C_1117) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_9658])).

tff(c_9830,plain,(
    ! [A_1040,B_1041,C_1042] :
      ( r2_orders_2(A_1040,'#skF_1'(k3_orders_2(A_1040,B_1041,C_1042)),C_1042)
      | ~ m1_subset_1(C_1042,u1_struct_0(A_1040))
      | ~ m1_subset_1(B_1041,k1_zfmisc_1(u1_struct_0(A_1040)))
      | ~ l1_orders_2(A_1040)
      | ~ v5_orders_2(A_1040)
      | ~ v4_orders_2(A_1040)
      | ~ v3_orders_2(A_1040)
      | v2_struct_0(A_1040)
      | k3_orders_2(A_1040,B_1041,C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_9824])).

tff(c_38,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_9567,plain,(
    ! [B_1057,D_1058,A_1059,C_1060] :
      ( r2_hidden(B_1057,D_1058)
      | ~ r2_hidden(B_1057,k3_orders_2(A_1059,D_1058,C_1060))
      | ~ m1_subset_1(D_1058,k1_zfmisc_1(u1_struct_0(A_1059)))
      | ~ m1_subset_1(C_1060,u1_struct_0(A_1059))
      | ~ m1_subset_1(B_1057,u1_struct_0(A_1059))
      | ~ l1_orders_2(A_1059)
      | ~ v5_orders_2(A_1059)
      | ~ v4_orders_2(A_1059)
      | ~ v3_orders_2(A_1059)
      | v2_struct_0(A_1059) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_9735,plain,(
    ! [A_1099,D_1100,C_1101] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_1099,D_1100,C_1101)),D_1100)
      | ~ m1_subset_1(D_1100,k1_zfmisc_1(u1_struct_0(A_1099)))
      | ~ m1_subset_1(C_1101,u1_struct_0(A_1099))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1099,D_1100,C_1101)),u1_struct_0(A_1099))
      | ~ l1_orders_2(A_1099)
      | ~ v5_orders_2(A_1099)
      | ~ v4_orders_2(A_1099)
      | ~ v3_orders_2(A_1099)
      | v2_struct_0(A_1099)
      | k3_orders_2(A_1099,D_1100,C_1101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_9567])).

tff(c_9747,plain,(
    ! [A_1104,B_1105,C_1106] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_1104,B_1105,C_1106)),B_1105)
      | ~ m1_subset_1(C_1106,u1_struct_0(A_1104))
      | ~ m1_subset_1(B_1105,k1_zfmisc_1(u1_struct_0(A_1104)))
      | ~ l1_orders_2(A_1104)
      | ~ v5_orders_2(A_1104)
      | ~ v4_orders_2(A_1104)
      | ~ v3_orders_2(A_1104)
      | v2_struct_0(A_1104)
      | k3_orders_2(A_1104,B_1105,C_1106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_9735])).

tff(c_9369,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9366,c_2])).

tff(c_9740,plain,(
    ! [D_1100,C_1101] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),D_1100)
      | ~ m1_subset_1(D_1100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1101,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_1100,C_1101) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9369,c_9735])).

tff(c_9744,plain,(
    ! [D_1100,C_1101] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),D_1100)
      | ~ m1_subset_1(D_1100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1101,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_1100,C_1101) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9740])).

tff(c_9745,plain,(
    ! [D_1100,C_1101] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),D_1100)
      | ~ m1_subset_1(D_1100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1101,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_1100,C_1101) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1100,C_1101)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9744])).

tff(c_9750,plain,(
    ! [C_1106] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1106)),'#skF_5')
      | ~ m1_subset_1(C_1106,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9747,c_9745])).

tff(c_9778,plain,(
    ! [C_1106] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1106)),'#skF_5')
      | ~ m1_subset_1(C_1106,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1106) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_9750])).

tff(c_9779,plain,(
    ! [C_1106] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1106)),'#skF_5')
      | ~ m1_subset_1(C_1106,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1106) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9778])).

tff(c_9794,plain,(
    ! [A_1108,D_1109,B_1110,E_1111] :
      ( r3_orders_2(A_1108,k1_funct_1(D_1109,u1_struct_0(A_1108)),B_1110)
      | ~ r2_hidden(B_1110,E_1111)
      | ~ m2_orders_2(E_1111,A_1108,D_1109)
      | ~ m1_orders_1(D_1109,k1_orders_1(u1_struct_0(A_1108)))
      | ~ m1_subset_1(k1_funct_1(D_1109,u1_struct_0(A_1108)),u1_struct_0(A_1108))
      | ~ m1_subset_1(B_1110,u1_struct_0(A_1108))
      | ~ l1_orders_2(A_1108)
      | ~ v5_orders_2(A_1108)
      | ~ v4_orders_2(A_1108)
      | ~ v3_orders_2(A_1108)
      | v2_struct_0(A_1108) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_9846,plain,(
    ! [A_1120,D_1121,C_1122] :
      ( r3_orders_2(A_1120,k1_funct_1(D_1121,u1_struct_0(A_1120)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)))
      | ~ m2_orders_2('#skF_5',A_1120,D_1121)
      | ~ m1_orders_1(D_1121,k1_orders_1(u1_struct_0(A_1120)))
      | ~ m1_subset_1(k1_funct_1(D_1121,u1_struct_0(A_1120)),u1_struct_0(A_1120))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)),u1_struct_0(A_1120))
      | ~ l1_orders_2(A_1120)
      | ~ v5_orders_2(A_1120)
      | ~ v4_orders_2(A_1120)
      | ~ v3_orders_2(A_1120)
      | v2_struct_0(A_1120)
      | ~ m1_subset_1(C_1122,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1122) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9779,c_9794])).

tff(c_9851,plain,(
    ! [C_1122] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1122,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1122) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_9846])).

tff(c_9854,plain,(
    ! [C_1122] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1122)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1122,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1122) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_38,c_42,c_40,c_9851])).

tff(c_9856,plain,(
    ! [C_1123] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1123)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1123)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1123,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1123) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9854])).

tff(c_9860,plain,(
    ! [C_1042] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_9856])).

tff(c_9866,plain,(
    ! [C_1042] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_9860])).

tff(c_9869,plain,(
    ! [C_1124] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1124)))
      | ~ m1_subset_1(C_1124,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1124) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9866])).

tff(c_22,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_orders_2(A_40,B_41,C_42)
      | ~ r3_orders_2(A_40,B_41,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_40))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9871,plain,(
    ! [C_1124] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1124)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1124)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1124,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1124) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9869,c_22])).

tff(c_9874,plain,(
    ! [C_1124] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1124)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1124)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1124,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1124) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_9871])).

tff(c_9876,plain,(
    ! [C_1125] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1125)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1125)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1125,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1125) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9874])).

tff(c_9880,plain,(
    ! [C_1042] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_9876])).

tff(c_9886,plain,(
    ! [C_1042] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_9880])).

tff(c_9889,plain,(
    ! [C_1126] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1126)))
      | ~ m1_subset_1(C_1126,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1126) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9886])).

tff(c_26,plain,(
    ! [A_43,C_55,D_57,B_51] :
      ( ~ r1_orders_2(A_43,C_55,D_57)
      | ~ r2_orders_2(A_43,B_51,C_55)
      | r2_orders_2(A_43,B_51,D_57)
      | ~ m1_subset_1(D_57,u1_struct_0(A_43))
      | ~ m1_subset_1(C_55,u1_struct_0(A_43))
      | ~ m1_subset_1(B_51,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9897,plain,(
    ! [B_51,C_1126] :
      ( ~ r2_orders_2('#skF_2',B_51,'#skF_3')
      | r2_orders_2('#skF_2',B_51,'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1126)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1126)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ m1_subset_1(C_1126,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1126) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9889,c_26])).

tff(c_10262,plain,(
    ! [B_1163,C_1164] :
      ( ~ r2_orders_2('#skF_2',B_1163,'#skF_3')
      | r2_orders_2('#skF_2',B_1163,'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1164)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1164)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1163,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1164,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1164) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_9897])).

tff(c_10265,plain,(
    ! [B_1163,C_1042] :
      ( ~ r2_orders_2('#skF_2',B_1163,'#skF_3')
      | r2_orders_2('#skF_2',B_1163,'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(B_1163,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_10262])).

tff(c_10271,plain,(
    ! [B_1163,C_1042] :
      ( ~ r2_orders_2('#skF_2',B_1163,'#skF_3')
      | r2_orders_2('#skF_2',B_1163,'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)))
      | ~ m1_subset_1(B_1163,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_10265])).

tff(c_10274,plain,(
    ! [B_1165,C_1166] :
      ( ~ r2_orders_2('#skF_2',B_1165,'#skF_3')
      | r2_orders_2('#skF_2',B_1165,'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1166)))
      | ~ m1_subset_1(B_1165,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1166,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1166) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10271])).

tff(c_10,plain,(
    ! [A_26,C_32] :
      ( ~ r2_orders_2(A_26,C_32,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10281,plain,(
    ! [C_1166] :
      ( ~ l1_orders_2('#skF_2')
      | ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1166)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1166)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1166,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1166) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10274,c_10])).

tff(c_10291,plain,(
    ! [C_1167] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1167)),'#skF_3')
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1167)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1167,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1167) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10281])).

tff(c_10295,plain,(
    ! [C_1042] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)),'#skF_3')
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9488,c_10291])).

tff(c_10301,plain,(
    ! [C_1042] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1042)),'#skF_3')
      | ~ m1_subset_1(C_1042,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_1042) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_10295])).

tff(c_10305,plain,(
    ! [C_1175] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_1175)),'#skF_3')
      | ~ m1_subset_1(C_1175,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_1175) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10301])).

tff(c_10309,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9830,c_10305])).

tff(c_10337,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_9366,c_44,c_10309])).

tff(c_10339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_54,c_10337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.63  
% 9.57/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.63  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.57/3.63  
% 9.57/3.63  %Foreground sorts:
% 9.57/3.63  
% 9.57/3.63  
% 9.57/3.63  %Background operators:
% 9.57/3.63  
% 9.57/3.63  
% 9.57/3.63  %Foreground operators:
% 9.57/3.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.57/3.63  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 9.57/3.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.57/3.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.57/3.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.57/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.57/3.63  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 9.57/3.63  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 9.57/3.63  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 9.57/3.63  tff('#skF_5', type, '#skF_5': $i).
% 9.57/3.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.57/3.63  tff('#skF_2', type, '#skF_2': $i).
% 9.57/3.63  tff('#skF_3', type, '#skF_3': $i).
% 9.57/3.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.57/3.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.57/3.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.57/3.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.57/3.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.57/3.63  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.63  tff('#skF_4', type, '#skF_4': $i).
% 9.57/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.63  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 9.57/3.63  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 9.57/3.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.57/3.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.57/3.63  
% 9.57/3.65  tff(f_224, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 9.57/3.65  tff(f_104, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 9.57/3.65  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 9.57/3.65  tff(f_84, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 9.57/3.65  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.57/3.65  tff(f_170, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 9.57/3.65  tff(f_199, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 9.57/3.65  tff(f_119, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.57/3.65  tff(f_144, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 9.57/3.65  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 9.57/3.65  tff(c_36, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_52, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_50, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_48, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_46, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_42, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_40, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_9360, plain, (![C_1009, A_1010, B_1011]: (m1_subset_1(C_1009, k1_zfmisc_1(u1_struct_0(A_1010))) | ~m2_orders_2(C_1009, A_1010, B_1011) | ~m1_orders_1(B_1011, k1_orders_1(u1_struct_0(A_1010))) | ~l1_orders_2(A_1010) | ~v5_orders_2(A_1010) | ~v4_orders_2(A_1010) | ~v3_orders_2(A_1010) | v2_struct_0(A_1010))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.57/3.65  tff(c_9362, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_9360])).
% 9.57/3.65  tff(c_9365, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_42, c_9362])).
% 9.57/3.65  tff(c_9366, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_9365])).
% 9.57/3.65  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.57/3.65  tff(c_9390, plain, (![A_1013, B_1014, C_1015]: (m1_subset_1(k3_orders_2(A_1013, B_1014, C_1015), k1_zfmisc_1(u1_struct_0(A_1013))) | ~m1_subset_1(C_1015, u1_struct_0(A_1013)) | ~m1_subset_1(B_1014, k1_zfmisc_1(u1_struct_0(A_1013))) | ~l1_orders_2(A_1013) | ~v5_orders_2(A_1013) | ~v4_orders_2(A_1013) | ~v3_orders_2(A_1013) | v2_struct_0(A_1013))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.57/3.65  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.57/3.65  tff(c_9484, plain, (![A_1039, A_1040, B_1041, C_1042]: (m1_subset_1(A_1039, u1_struct_0(A_1040)) | ~r2_hidden(A_1039, k3_orders_2(A_1040, B_1041, C_1042)) | ~m1_subset_1(C_1042, u1_struct_0(A_1040)) | ~m1_subset_1(B_1041, k1_zfmisc_1(u1_struct_0(A_1040))) | ~l1_orders_2(A_1040) | ~v5_orders_2(A_1040) | ~v4_orders_2(A_1040) | ~v3_orders_2(A_1040) | v2_struct_0(A_1040))), inference(resolution, [status(thm)], [c_9390, c_2])).
% 9.57/3.65  tff(c_9488, plain, (![A_1040, B_1041, C_1042]: (m1_subset_1('#skF_1'(k3_orders_2(A_1040, B_1041, C_1042)), u1_struct_0(A_1040)) | ~m1_subset_1(C_1042, u1_struct_0(A_1040)) | ~m1_subset_1(B_1041, k1_zfmisc_1(u1_struct_0(A_1040))) | ~l1_orders_2(A_1040) | ~v5_orders_2(A_1040) | ~v4_orders_2(A_1040) | ~v3_orders_2(A_1040) | v2_struct_0(A_1040) | k3_orders_2(A_1040, B_1041, C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_9484])).
% 9.57/3.65  tff(c_9658, plain, (![A_1077, B_1078, C_1079, D_1080]: (r2_orders_2(A_1077, B_1078, C_1079) | ~r2_hidden(B_1078, k3_orders_2(A_1077, D_1080, C_1079)) | ~m1_subset_1(D_1080, k1_zfmisc_1(u1_struct_0(A_1077))) | ~m1_subset_1(C_1079, u1_struct_0(A_1077)) | ~m1_subset_1(B_1078, u1_struct_0(A_1077)) | ~l1_orders_2(A_1077) | ~v5_orders_2(A_1077) | ~v4_orders_2(A_1077) | ~v3_orders_2(A_1077) | v2_struct_0(A_1077))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.57/3.65  tff(c_9824, plain, (![A_1115, D_1116, C_1117]: (r2_orders_2(A_1115, '#skF_1'(k3_orders_2(A_1115, D_1116, C_1117)), C_1117) | ~m1_subset_1(D_1116, k1_zfmisc_1(u1_struct_0(A_1115))) | ~m1_subset_1(C_1117, u1_struct_0(A_1115)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1115, D_1116, C_1117)), u1_struct_0(A_1115)) | ~l1_orders_2(A_1115) | ~v5_orders_2(A_1115) | ~v4_orders_2(A_1115) | ~v3_orders_2(A_1115) | v2_struct_0(A_1115) | k3_orders_2(A_1115, D_1116, C_1117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_9658])).
% 9.57/3.65  tff(c_9830, plain, (![A_1040, B_1041, C_1042]: (r2_orders_2(A_1040, '#skF_1'(k3_orders_2(A_1040, B_1041, C_1042)), C_1042) | ~m1_subset_1(C_1042, u1_struct_0(A_1040)) | ~m1_subset_1(B_1041, k1_zfmisc_1(u1_struct_0(A_1040))) | ~l1_orders_2(A_1040) | ~v5_orders_2(A_1040) | ~v4_orders_2(A_1040) | ~v3_orders_2(A_1040) | v2_struct_0(A_1040) | k3_orders_2(A_1040, B_1041, C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_9824])).
% 9.57/3.65  tff(c_38, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_224])).
% 9.57/3.65  tff(c_9567, plain, (![B_1057, D_1058, A_1059, C_1060]: (r2_hidden(B_1057, D_1058) | ~r2_hidden(B_1057, k3_orders_2(A_1059, D_1058, C_1060)) | ~m1_subset_1(D_1058, k1_zfmisc_1(u1_struct_0(A_1059))) | ~m1_subset_1(C_1060, u1_struct_0(A_1059)) | ~m1_subset_1(B_1057, u1_struct_0(A_1059)) | ~l1_orders_2(A_1059) | ~v5_orders_2(A_1059) | ~v4_orders_2(A_1059) | ~v3_orders_2(A_1059) | v2_struct_0(A_1059))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.57/3.65  tff(c_9735, plain, (![A_1099, D_1100, C_1101]: (r2_hidden('#skF_1'(k3_orders_2(A_1099, D_1100, C_1101)), D_1100) | ~m1_subset_1(D_1100, k1_zfmisc_1(u1_struct_0(A_1099))) | ~m1_subset_1(C_1101, u1_struct_0(A_1099)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1099, D_1100, C_1101)), u1_struct_0(A_1099)) | ~l1_orders_2(A_1099) | ~v5_orders_2(A_1099) | ~v4_orders_2(A_1099) | ~v3_orders_2(A_1099) | v2_struct_0(A_1099) | k3_orders_2(A_1099, D_1100, C_1101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_9567])).
% 9.57/3.65  tff(c_9747, plain, (![A_1104, B_1105, C_1106]: (r2_hidden('#skF_1'(k3_orders_2(A_1104, B_1105, C_1106)), B_1105) | ~m1_subset_1(C_1106, u1_struct_0(A_1104)) | ~m1_subset_1(B_1105, k1_zfmisc_1(u1_struct_0(A_1104))) | ~l1_orders_2(A_1104) | ~v5_orders_2(A_1104) | ~v4_orders_2(A_1104) | ~v3_orders_2(A_1104) | v2_struct_0(A_1104) | k3_orders_2(A_1104, B_1105, C_1106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_9735])).
% 9.57/3.65  tff(c_9369, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_9366, c_2])).
% 9.57/3.65  tff(c_9740, plain, (![D_1100, C_1101]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), D_1100) | ~m1_subset_1(D_1100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1101, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_1100, C_1101)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), '#skF_5'))), inference(resolution, [status(thm)], [c_9369, c_9735])).
% 9.57/3.65  tff(c_9744, plain, (![D_1100, C_1101]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), D_1100) | ~m1_subset_1(D_1100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1101, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_1100, C_1101)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9740])).
% 9.57/3.65  tff(c_9745, plain, (![D_1100, C_1101]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), D_1100) | ~m1_subset_1(D_1100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1101, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_1100, C_1101)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1100, C_1101)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_9744])).
% 9.57/3.65  tff(c_9750, plain, (![C_1106]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1106)), '#skF_5') | ~m1_subset_1(C_1106, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9747, c_9745])).
% 9.57/3.65  tff(c_9778, plain, (![C_1106]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1106)), '#skF_5') | ~m1_subset_1(C_1106, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_9750])).
% 9.57/3.65  tff(c_9779, plain, (![C_1106]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1106)), '#skF_5') | ~m1_subset_1(C_1106, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1106)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_9778])).
% 9.57/3.65  tff(c_9794, plain, (![A_1108, D_1109, B_1110, E_1111]: (r3_orders_2(A_1108, k1_funct_1(D_1109, u1_struct_0(A_1108)), B_1110) | ~r2_hidden(B_1110, E_1111) | ~m2_orders_2(E_1111, A_1108, D_1109) | ~m1_orders_1(D_1109, k1_orders_1(u1_struct_0(A_1108))) | ~m1_subset_1(k1_funct_1(D_1109, u1_struct_0(A_1108)), u1_struct_0(A_1108)) | ~m1_subset_1(B_1110, u1_struct_0(A_1108)) | ~l1_orders_2(A_1108) | ~v5_orders_2(A_1108) | ~v4_orders_2(A_1108) | ~v3_orders_2(A_1108) | v2_struct_0(A_1108))), inference(cnfTransformation, [status(thm)], [f_199])).
% 9.57/3.65  tff(c_9846, plain, (![A_1120, D_1121, C_1122]: (r3_orders_2(A_1120, k1_funct_1(D_1121, u1_struct_0(A_1120)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122))) | ~m2_orders_2('#skF_5', A_1120, D_1121) | ~m1_orders_1(D_1121, k1_orders_1(u1_struct_0(A_1120))) | ~m1_subset_1(k1_funct_1(D_1121, u1_struct_0(A_1120)), u1_struct_0(A_1120)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122)), u1_struct_0(A_1120)) | ~l1_orders_2(A_1120) | ~v5_orders_2(A_1120) | ~v4_orders_2(A_1120) | ~v3_orders_2(A_1120) | v2_struct_0(A_1120) | ~m1_subset_1(C_1122, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1122)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9779, c_9794])).
% 9.57/3.65  tff(c_9851, plain, (![C_1122]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_1122, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1122)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_9846])).
% 9.57/3.65  tff(c_9854, plain, (![C_1122]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1122)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_1122, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_38, c_42, c_40, c_9851])).
% 9.57/3.65  tff(c_9856, plain, (![C_1123]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1123))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1123)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1123, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1123)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_9854])).
% 9.57/3.65  tff(c_9860, plain, (![C_1042]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_9856])).
% 9.57/3.65  tff(c_9866, plain, (![C_1042]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_9860])).
% 9.57/3.65  tff(c_9869, plain, (![C_1124]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1124))) | ~m1_subset_1(C_1124, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1124)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_9866])).
% 9.57/3.65  tff(c_22, plain, (![A_40, B_41, C_42]: (r1_orders_2(A_40, B_41, C_42) | ~r3_orders_2(A_40, B_41, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_40)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.57/3.65  tff(c_9871, plain, (![C_1124]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1124))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1124)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_1124, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9869, c_22])).
% 9.57/3.65  tff(c_9874, plain, (![C_1124]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1124))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1124)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_1124, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1124)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_9871])).
% 9.57/3.65  tff(c_9876, plain, (![C_1125]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1125))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1125)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1125, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1125)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_9874])).
% 9.57/3.65  tff(c_9880, plain, (![C_1042]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_9876])).
% 9.57/3.65  tff(c_9886, plain, (![C_1042]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_9880])).
% 9.57/3.65  tff(c_9889, plain, (![C_1126]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1126))) | ~m1_subset_1(C_1126, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1126)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_9886])).
% 9.57/3.65  tff(c_26, plain, (![A_43, C_55, D_57, B_51]: (~r1_orders_2(A_43, C_55, D_57) | ~r2_orders_2(A_43, B_51, C_55) | r2_orders_2(A_43, B_51, D_57) | ~m1_subset_1(D_57, u1_struct_0(A_43)) | ~m1_subset_1(C_55, u1_struct_0(A_43)) | ~m1_subset_1(B_51, u1_struct_0(A_43)) | ~l1_orders_2(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.57/3.65  tff(c_9897, plain, (![B_51, C_1126]: (~r2_orders_2('#skF_2', B_51, '#skF_3') | r2_orders_2('#skF_2', B_51, '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1126))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1126)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_51, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~m1_subset_1(C_1126, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9889, c_26])).
% 9.57/3.65  tff(c_10262, plain, (![B_1163, C_1164]: (~r2_orders_2('#skF_2', B_1163, '#skF_3') | r2_orders_2('#skF_2', B_1163, '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1164))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1164)), u1_struct_0('#skF_2')) | ~m1_subset_1(B_1163, u1_struct_0('#skF_2')) | ~m1_subset_1(C_1164, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_9897])).
% 9.57/3.65  tff(c_10265, plain, (![B_1163, C_1042]: (~r2_orders_2('#skF_2', B_1163, '#skF_3') | r2_orders_2('#skF_2', B_1163, '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(B_1163, u1_struct_0('#skF_2')) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_10262])).
% 9.57/3.65  tff(c_10271, plain, (![B_1163, C_1042]: (~r2_orders_2('#skF_2', B_1163, '#skF_3') | r2_orders_2('#skF_2', B_1163, '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042))) | ~m1_subset_1(B_1163, u1_struct_0('#skF_2')) | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_10265])).
% 9.57/3.65  tff(c_10274, plain, (![B_1165, C_1166]: (~r2_orders_2('#skF_2', B_1165, '#skF_3') | r2_orders_2('#skF_2', B_1165, '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1166))) | ~m1_subset_1(B_1165, u1_struct_0('#skF_2')) | ~m1_subset_1(C_1166, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1166)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_10271])).
% 9.57/3.65  tff(c_10, plain, (![A_26, C_32]: (~r2_orders_2(A_26, C_32, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.57/3.65  tff(c_10281, plain, (![C_1166]: (~l1_orders_2('#skF_2') | ~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1166)), '#skF_3') | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1166)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1166, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1166)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10274, c_10])).
% 9.57/3.65  tff(c_10291, plain, (![C_1167]: (~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1167)), '#skF_3') | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1167)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1167, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10281])).
% 9.57/3.65  tff(c_10295, plain, (![C_1042]: (~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042)), '#skF_3') | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9488, c_10291])).
% 9.57/3.65  tff(c_10301, plain, (![C_1042]: (~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1042)), '#skF_3') | ~m1_subset_1(C_1042, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_1042)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_10295])).
% 9.57/3.65  tff(c_10305, plain, (![C_1175]: (~r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_1175)), '#skF_3') | ~m1_subset_1(C_1175, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_1175)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_10301])).
% 9.57/3.65  tff(c_10309, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9830, c_10305])).
% 9.57/3.65  tff(c_10337, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_9366, c_44, c_10309])).
% 9.57/3.65  tff(c_10339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_54, c_10337])).
% 9.57/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.57/3.65  
% 9.57/3.65  Inference rules
% 9.57/3.65  ----------------------
% 9.57/3.65  #Ref     : 0
% 9.57/3.65  #Sup     : 1983
% 9.57/3.65  #Fact    : 0
% 9.57/3.65  #Define  : 0
% 9.57/3.65  #Split   : 14
% 9.57/3.65  #Chain   : 0
% 9.57/3.65  #Close   : 0
% 9.57/3.65  
% 9.57/3.65  Ordering : KBO
% 9.57/3.65  
% 9.57/3.65  Simplification rules
% 9.57/3.65  ----------------------
% 9.57/3.65  #Subsume      : 855
% 9.57/3.65  #Demod        : 3168
% 9.57/3.65  #Tautology    : 142
% 9.57/3.65  #SimpNegUnit  : 449
% 9.57/3.65  #BackRed      : 108
% 9.57/3.65  
% 9.57/3.65  #Partial instantiations: 0
% 9.57/3.65  #Strategies tried      : 1
% 9.57/3.65  
% 9.57/3.65  Timing (in seconds)
% 9.57/3.65  ----------------------
% 9.86/3.66  Preprocessing        : 0.43
% 9.86/3.66  Parsing              : 0.26
% 9.86/3.66  CNF conversion       : 0.04
% 9.86/3.66  Main loop            : 2.39
% 9.86/3.66  Inferencing          : 0.73
% 9.86/3.66  Reduction            : 0.71
% 9.86/3.66  Demodulation         : 0.46
% 9.86/3.66  BG Simplification    : 0.07
% 9.86/3.66  Subsumption          : 0.76
% 9.86/3.66  Abstraction          : 0.11
% 9.86/3.66  MUC search           : 0.00
% 9.86/3.66  Cooper               : 0.00
% 9.86/3.66  Total                : 2.86
% 9.86/3.66  Index Insertion      : 0.00
% 9.86/3.66  Index Deletion       : 0.00
% 9.86/3.66  Index Matching       : 0.00
% 9.86/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
