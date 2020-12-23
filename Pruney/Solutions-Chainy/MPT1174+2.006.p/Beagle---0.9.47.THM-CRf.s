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
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 752 expanded)
%              Number of leaves         :   38 ( 310 expanded)
%              Depth                    :   25
%              Number of atoms          :  690 (4094 expanded)
%              Number of equality atoms :   86 ( 581 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_219,negated_conjecture,(
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

tff(f_99,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_194,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_62,axiom,(
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

tff(f_139,axiom,(
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

tff(f_79,axiom,(
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

tff(f_165,axiom,(
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

tff(c_38,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_44,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_42,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_6478,plain,(
    ! [C_755,A_756,B_757] :
      ( m1_subset_1(C_755,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ m2_orders_2(C_755,A_756,B_757)
      | ~ m1_orders_1(B_757,k1_orders_1(u1_struct_0(A_756)))
      | ~ l1_orders_2(A_756)
      | ~ v5_orders_2(A_756)
      | ~ v4_orders_2(A_756)
      | ~ v3_orders_2(A_756)
      | v2_struct_0(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6480,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_6478])).

tff(c_6483,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_44,c_6480])).

tff(c_6484,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6483])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6487,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6484,c_2])).

tff(c_40,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_4,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6826,plain,(
    ! [A_838,D_839,B_840,E_841] :
      ( r3_orders_2(A_838,k1_funct_1(D_839,u1_struct_0(A_838)),B_840)
      | ~ r2_hidden(B_840,E_841)
      | ~ m2_orders_2(E_841,A_838,D_839)
      | ~ m1_orders_1(D_839,k1_orders_1(u1_struct_0(A_838)))
      | ~ m1_subset_1(k1_funct_1(D_839,u1_struct_0(A_838)),u1_struct_0(A_838))
      | ~ m1_subset_1(B_840,u1_struct_0(A_838))
      | ~ l1_orders_2(A_838)
      | ~ v5_orders_2(A_838)
      | ~ v4_orders_2(A_838)
      | ~ v3_orders_2(A_838)
      | v2_struct_0(A_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8729,plain,(
    ! [A_1082,D_1083,A_1084] :
      ( r3_orders_2(A_1082,k1_funct_1(D_1083,u1_struct_0(A_1082)),'#skF_1'(A_1084))
      | ~ m2_orders_2(A_1084,A_1082,D_1083)
      | ~ m1_orders_1(D_1083,k1_orders_1(u1_struct_0(A_1082)))
      | ~ m1_subset_1(k1_funct_1(D_1083,u1_struct_0(A_1082)),u1_struct_0(A_1082))
      | ~ m1_subset_1('#skF_1'(A_1084),u1_struct_0(A_1082))
      | ~ l1_orders_2(A_1082)
      | ~ v5_orders_2(A_1082)
      | ~ v4_orders_2(A_1082)
      | ~ v3_orders_2(A_1082)
      | v2_struct_0(A_1082)
      | k1_xboole_0 = A_1084 ) ),
    inference(resolution,[status(thm)],[c_4,c_6826])).

tff(c_8734,plain,(
    ! [A_1084] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1084))
      | ~ m2_orders_2(A_1084,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1084),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = A_1084 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8729])).

tff(c_8737,plain,(
    ! [A_1084] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1084))
      | ~ m2_orders_2(A_1084,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_1084),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = A_1084 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_40,c_44,c_8734])).

tff(c_8739,plain,(
    ! [A_1085] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1085))
      | ~ m2_orders_2(A_1085,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_1085),u1_struct_0('#skF_2'))
      | k1_xboole_0 = A_1085 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_8737])).

tff(c_8752,plain,(
    ! [A_1086] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_1086))
      | ~ m2_orders_2(A_1086,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1086
      | ~ r2_hidden('#skF_1'(A_1086),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_8739])).

tff(c_24,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_orders_2(A_28,B_29,C_30)
      | ~ r3_orders_2(A_28,B_29,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_28))
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8754,plain,(
    ! [A_1086] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1086))
      | ~ m1_subset_1('#skF_1'(A_1086),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(A_1086,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1086
      | ~ r2_hidden('#skF_1'(A_1086),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8752,c_24])).

tff(c_8757,plain,(
    ! [A_1086] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1086))
      | ~ m1_subset_1('#skF_1'(A_1086),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(A_1086,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1086
      | ~ r2_hidden('#skF_1'(A_1086),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_8754])).

tff(c_8759,plain,(
    ! [A_1087] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1087))
      | ~ m1_subset_1('#skF_1'(A_1087),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(A_1087,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1087
      | ~ r2_hidden('#skF_1'(A_1087),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_8757])).

tff(c_8779,plain,(
    ! [A_1090] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_1090))
      | ~ m2_orders_2(A_1090,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1090
      | ~ r2_hidden('#skF_1'(A_1090),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_8759])).

tff(c_6488,plain,(
    ! [A_758] :
      ( m1_subset_1(A_758,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_758,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6484,c_2])).

tff(c_75,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_orders_2(A_122,B_123,C_124)
      | C_124 = B_123
      | ~ r1_orders_2(A_122,B_123,C_124)
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    ! [B_123] :
      ( r2_orders_2('#skF_2',B_123,'#skF_3')
      | B_123 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_123,'#skF_3')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_80,plain,(
    ! [B_123] :
      ( r2_orders_2('#skF_2',B_123,'#skF_3')
      | B_123 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_123,'#skF_3')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_77])).

tff(c_6504,plain,(
    ! [A_758] :
      ( r2_orders_2('#skF_2',A_758,'#skF_3')
      | A_758 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_758,'#skF_3')
      | ~ r2_hidden(A_758,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6488,c_80])).

tff(c_6597,plain,(
    ! [A_782,C_783,D_784,B_785] :
      ( ~ r2_orders_2(A_782,C_783,D_784)
      | ~ r1_orders_2(A_782,B_785,C_783)
      | r2_orders_2(A_782,B_785,D_784)
      | ~ m1_subset_1(D_784,u1_struct_0(A_782))
      | ~ m1_subset_1(C_783,u1_struct_0(A_782))
      | ~ m1_subset_1(B_785,u1_struct_0(A_782))
      | ~ l1_orders_2(A_782)
      | ~ v5_orders_2(A_782)
      | ~ v4_orders_2(A_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6603,plain,(
    ! [B_785,A_758] :
      ( ~ r1_orders_2('#skF_2',B_785,A_758)
      | r2_orders_2('#skF_2',B_785,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_758,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_785,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_758 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_758,'#skF_3')
      | ~ r2_hidden(A_758,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6504,c_6597])).

tff(c_6612,plain,(
    ! [B_785,A_758] :
      ( ~ r1_orders_2('#skF_2',B_785,A_758)
      | r2_orders_2('#skF_2',B_785,'#skF_3')
      | ~ m1_subset_1(A_758,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_785,u1_struct_0('#skF_2'))
      | A_758 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_758,'#skF_3')
      | ~ r2_hidden(A_758,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_6603])).

tff(c_8788,plain,(
    ! [A_1090] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_1090),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | '#skF_1'(A_1090) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_1090),'#skF_3')
      | ~ m2_orders_2(A_1090,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1090
      | ~ r2_hidden('#skF_1'(A_1090),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8779,c_6612])).

tff(c_8800,plain,(
    ! [A_1090] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_1090),u1_struct_0('#skF_2'))
      | '#skF_1'(A_1090) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_1090),'#skF_3')
      | ~ m2_orders_2(A_1090,'#skF_2','#skF_4')
      | k1_xboole_0 = A_1090
      | ~ r2_hidden('#skF_1'(A_1090),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8788])).

tff(c_8804,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8800])).

tff(c_12,plain,(
    ! [A_14,C_20] :
      ( ~ r2_orders_2(A_14,C_20,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8810,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_8804,c_12])).

tff(c_8820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_8810])).

tff(c_8822,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_8800])).

tff(c_6535,plain,(
    ! [A_763,B_764,C_765] :
      ( m1_subset_1(k3_orders_2(A_763,B_764,C_765),k1_zfmisc_1(u1_struct_0(A_763)))
      | ~ m1_subset_1(C_765,u1_struct_0(A_763))
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0(A_763)))
      | ~ l1_orders_2(A_763)
      | ~ v5_orders_2(A_763)
      | ~ v4_orders_2(A_763)
      | ~ v3_orders_2(A_763)
      | v2_struct_0(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6586,plain,(
    ! [A_774,A_775,B_776,C_777] :
      ( m1_subset_1(A_774,u1_struct_0(A_775))
      | ~ r2_hidden(A_774,k3_orders_2(A_775,B_776,C_777))
      | ~ m1_subset_1(C_777,u1_struct_0(A_775))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_775)))
      | ~ l1_orders_2(A_775)
      | ~ v5_orders_2(A_775)
      | ~ v4_orders_2(A_775)
      | ~ v3_orders_2(A_775)
      | v2_struct_0(A_775) ) ),
    inference(resolution,[status(thm)],[c_6535,c_2])).

tff(c_6590,plain,(
    ! [A_775,B_776,C_777] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_775,B_776,C_777)),u1_struct_0(A_775))
      | ~ m1_subset_1(C_777,u1_struct_0(A_775))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_775)))
      | ~ l1_orders_2(A_775)
      | ~ v5_orders_2(A_775)
      | ~ v4_orders_2(A_775)
      | ~ v3_orders_2(A_775)
      | v2_struct_0(A_775)
      | k3_orders_2(A_775,B_776,C_777) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6586])).

tff(c_6620,plain,(
    ! [B_788,D_789,A_790,C_791] :
      ( r2_hidden(B_788,D_789)
      | ~ r2_hidden(B_788,k3_orders_2(A_790,D_789,C_791))
      | ~ m1_subset_1(D_789,k1_zfmisc_1(u1_struct_0(A_790)))
      | ~ m1_subset_1(C_791,u1_struct_0(A_790))
      | ~ m1_subset_1(B_788,u1_struct_0(A_790))
      | ~ l1_orders_2(A_790)
      | ~ v5_orders_2(A_790)
      | ~ v4_orders_2(A_790)
      | ~ v3_orders_2(A_790)
      | v2_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6833,plain,(
    ! [A_842,D_843,C_844] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_842,D_843,C_844)),D_843)
      | ~ m1_subset_1(D_843,k1_zfmisc_1(u1_struct_0(A_842)))
      | ~ m1_subset_1(C_844,u1_struct_0(A_842))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_842,D_843,C_844)),u1_struct_0(A_842))
      | ~ l1_orders_2(A_842)
      | ~ v5_orders_2(A_842)
      | ~ v4_orders_2(A_842)
      | ~ v3_orders_2(A_842)
      | v2_struct_0(A_842)
      | k3_orders_2(A_842,D_843,C_844) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6620])).

tff(c_6845,plain,(
    ! [A_847,B_848,C_849] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_847,B_848,C_849)),B_848)
      | ~ m1_subset_1(C_849,u1_struct_0(A_847))
      | ~ m1_subset_1(B_848,k1_zfmisc_1(u1_struct_0(A_847)))
      | ~ l1_orders_2(A_847)
      | ~ v5_orders_2(A_847)
      | ~ v4_orders_2(A_847)
      | ~ v3_orders_2(A_847)
      | v2_struct_0(A_847)
      | k3_orders_2(A_847,B_848,C_849) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6590,c_6833])).

tff(c_6838,plain,(
    ! [D_843,C_844] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),D_843)
      | ~ m1_subset_1(D_843,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_844,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_843,C_844) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_6833])).

tff(c_6842,plain,(
    ! [D_843,C_844] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),D_843)
      | ~ m1_subset_1(D_843,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_844,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_843,C_844) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_6838])).

tff(c_6843,plain,(
    ! [D_843,C_844] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),D_843)
      | ~ m1_subset_1(D_843,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_844,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_843,C_844) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_843,C_844)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6842])).

tff(c_6848,plain,(
    ! [C_849] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_849)),'#skF_5')
      | ~ m1_subset_1(C_849,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_849) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6845,c_6843])).

tff(c_6866,plain,(
    ! [C_849] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_849)),'#skF_5')
      | ~ m1_subset_1(C_849,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_849) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_6484,c_6848])).

tff(c_6867,plain,(
    ! [C_849] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_849)),'#skF_5')
      | ~ m1_subset_1(C_849,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_849) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6866])).

tff(c_36,plain,(
    ! [A_61,D_89,B_77,E_91] :
      ( r3_orders_2(A_61,k1_funct_1(D_89,u1_struct_0(A_61)),B_77)
      | ~ r2_hidden(B_77,E_91)
      | ~ m2_orders_2(E_91,A_61,D_89)
      | ~ m1_orders_1(D_89,k1_orders_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(k1_funct_1(D_89,u1_struct_0(A_61)),u1_struct_0(A_61))
      | ~ m1_subset_1(B_77,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_11823,plain,(
    ! [B_1313,D_1314,A_1316,A_1317,C_1315] :
      ( r3_orders_2(A_1316,k1_funct_1(D_1314,u1_struct_0(A_1316)),'#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)))
      | ~ m2_orders_2(B_1313,A_1316,D_1314)
      | ~ m1_orders_1(D_1314,k1_orders_1(u1_struct_0(A_1316)))
      | ~ m1_subset_1(k1_funct_1(D_1314,u1_struct_0(A_1316)),u1_struct_0(A_1316))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)),u1_struct_0(A_1316))
      | ~ l1_orders_2(A_1316)
      | ~ v5_orders_2(A_1316)
      | ~ v4_orders_2(A_1316)
      | ~ v3_orders_2(A_1316)
      | v2_struct_0(A_1316)
      | ~ m1_subset_1(C_1315,u1_struct_0(A_1317))
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1317)))
      | ~ l1_orders_2(A_1317)
      | ~ v5_orders_2(A_1317)
      | ~ v4_orders_2(A_1317)
      | ~ v3_orders_2(A_1317)
      | v2_struct_0(A_1317)
      | k3_orders_2(A_1317,B_1313,C_1315) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6845,c_36])).

tff(c_11828,plain,(
    ! [A_1317,B_1313,C_1315] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)))
      | ~ m2_orders_2(B_1313,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1315,u1_struct_0(A_1317))
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1317)))
      | ~ l1_orders_2(A_1317)
      | ~ v5_orders_2(A_1317)
      | ~ v4_orders_2(A_1317)
      | ~ v3_orders_2(A_1317)
      | v2_struct_0(A_1317)
      | k3_orders_2(A_1317,B_1313,C_1315) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11823])).

tff(c_11831,plain,(
    ! [A_1317,B_1313,C_1315] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)))
      | ~ m2_orders_2(B_1313,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1317,B_1313,C_1315)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1315,u1_struct_0(A_1317))
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1317)))
      | ~ l1_orders_2(A_1317)
      | ~ v5_orders_2(A_1317)
      | ~ v4_orders_2(A_1317)
      | ~ v3_orders_2(A_1317)
      | v2_struct_0(A_1317)
      | k3_orders_2(A_1317,B_1313,C_1315) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_40,c_44,c_11828])).

tff(c_11833,plain,(
    ! [A_1318,B_1319,C_1320] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1318,B_1319,C_1320)))
      | ~ m2_orders_2(B_1319,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1318,B_1319,C_1320)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1320,u1_struct_0(A_1318))
      | ~ m1_subset_1(B_1319,k1_zfmisc_1(u1_struct_0(A_1318)))
      | ~ l1_orders_2(A_1318)
      | ~ v5_orders_2(A_1318)
      | ~ v4_orders_2(A_1318)
      | ~ v3_orders_2(A_1318)
      | v2_struct_0(A_1318)
      | k3_orders_2(A_1318,B_1319,C_1320) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11831])).

tff(c_11841,plain,(
    ! [B_776,C_777] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)))
      | ~ m2_orders_2(B_776,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6590,c_11833])).

tff(c_11851,plain,(
    ! [B_776,C_777] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)))
      | ~ m2_orders_2(B_776,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_11841])).

tff(c_11854,plain,(
    ! [B_1321,C_1322] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1321,C_1322)))
      | ~ m2_orders_2(B_1321,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1322,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1321,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1321,C_1322) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11851])).

tff(c_11856,plain,(
    ! [B_1321,C_1322] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1321,C_1322)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1321,C_1322)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_1321,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1322,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1321,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1321,C_1322) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11854,c_24])).

tff(c_11859,plain,(
    ! [B_1321,C_1322] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1321,C_1322)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1321,C_1322)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_1321,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1322,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1321,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1321,C_1322) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_11856])).

tff(c_11861,plain,(
    ! [B_1323,C_1324] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1323,C_1324)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1323,C_1324)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_1323,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1324,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1323,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1323,C_1324) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11859])).

tff(c_11869,plain,(
    ! [B_776,C_777] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)))
      | ~ m2_orders_2(B_776,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6590,c_11861])).

tff(c_11879,plain,(
    ! [B_776,C_777] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)))
      | ~ m2_orders_2(B_776,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_11869])).

tff(c_11882,plain,(
    ! [B_1325,C_1326] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1325,C_1326)))
      | ~ m2_orders_2(B_1325,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1326,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1325,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1325,C_1326) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11879])).

tff(c_6747,plain,(
    ! [A_809,B_810,C_811,D_812] :
      ( r2_orders_2(A_809,B_810,C_811)
      | ~ r2_hidden(B_810,k3_orders_2(A_809,D_812,C_811))
      | ~ m1_subset_1(D_812,k1_zfmisc_1(u1_struct_0(A_809)))
      | ~ m1_subset_1(C_811,u1_struct_0(A_809))
      | ~ m1_subset_1(B_810,u1_struct_0(A_809))
      | ~ l1_orders_2(A_809)
      | ~ v5_orders_2(A_809)
      | ~ v4_orders_2(A_809)
      | ~ v3_orders_2(A_809)
      | v2_struct_0(A_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8605,plain,(
    ! [A_1061,D_1062,C_1063] :
      ( r2_orders_2(A_1061,'#skF_1'(k3_orders_2(A_1061,D_1062,C_1063)),C_1063)
      | ~ m1_subset_1(D_1062,k1_zfmisc_1(u1_struct_0(A_1061)))
      | ~ m1_subset_1(C_1063,u1_struct_0(A_1061))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1061,D_1062,C_1063)),u1_struct_0(A_1061))
      | ~ l1_orders_2(A_1061)
      | ~ v5_orders_2(A_1061)
      | ~ v4_orders_2(A_1061)
      | ~ v3_orders_2(A_1061)
      | v2_struct_0(A_1061)
      | k3_orders_2(A_1061,D_1062,C_1063) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6747])).

tff(c_8610,plain,(
    ! [D_1062,C_1063] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_1062,C_1063)),C_1063)
      | ~ m1_subset_1(D_1062,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1063,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_1062,C_1063) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1062,C_1063)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_8605])).

tff(c_8614,plain,(
    ! [D_1062,C_1063] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_1062,C_1063)),C_1063)
      | ~ m1_subset_1(D_1062,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1063,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_1062,C_1063) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1062,C_1063)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_8610])).

tff(c_8616,plain,(
    ! [D_1064,C_1065] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_1064,C_1065)),C_1065)
      | ~ m1_subset_1(D_1064,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1065,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_1064,C_1065) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1064,C_1065)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_8614])).

tff(c_14,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_orders_2(A_14,B_18,C_20)
      | ~ r2_orders_2(A_14,B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ m1_subset_1(B_18,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8620,plain,(
    ! [D_1064,C_1065] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_1064,C_1065)),C_1065)
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_1064,C_1065)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1(D_1064,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1065,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_1064,C_1065) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1064,C_1065)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8616,c_14])).

tff(c_8634,plain,(
    ! [D_1069,C_1070] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_1069,C_1070)),C_1070)
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_1069,C_1070)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_1069,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1070,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_1069,C_1070) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_1069,C_1070)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8620])).

tff(c_8637,plain,(
    ! [B_776,C_777] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)),C_777)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_776,C_777)),'#skF_5')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6590,c_8634])).

tff(c_8643,plain,(
    ! [B_776,C_777] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_776,C_777)),C_777)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_776,C_777)),'#skF_5')
      | ~ m1_subset_1(C_777,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_776,C_777) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_8637])).

tff(c_8646,plain,(
    ! [B_1071,C_1072] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_1071,C_1072)),C_1072)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1071,C_1072)),'#skF_5')
      | ~ m1_subset_1(C_1072,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1071,C_1072) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_8643])).

tff(c_10,plain,(
    ! [A_14,B_18,C_20] :
      ( r2_orders_2(A_14,B_18,C_20)
      | C_20 = B_18
      | ~ r1_orders_2(A_14,B_18,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ m1_subset_1(B_18,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6498,plain,(
    ! [B_18,A_758] :
      ( r2_orders_2('#skF_2',B_18,A_758)
      | B_18 = A_758
      | ~ r1_orders_2('#skF_2',B_18,A_758)
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden(A_758,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6488,c_10])).

tff(c_6553,plain,(
    ! [B_769,A_770] :
      ( r2_orders_2('#skF_2',B_769,A_770)
      | B_769 = A_770
      | ~ r1_orders_2('#skF_2',B_769,A_770)
      | ~ m1_subset_1(B_769,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_770,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6498])).

tff(c_6559,plain,(
    ! [A_770] :
      ( r2_orders_2('#skF_2','#skF_3',A_770)
      | A_770 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_770)
      | ~ r2_hidden(A_770,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_6553])).

tff(c_6601,plain,(
    ! [B_785,A_770] :
      ( ~ r1_orders_2('#skF_2',B_785,'#skF_3')
      | r2_orders_2('#skF_2',B_785,A_770)
      | ~ m1_subset_1(A_770,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_785,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_770 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_770)
      | ~ r2_hidden(A_770,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6559,c_6597])).

tff(c_6625,plain,(
    ! [B_792,A_793] :
      ( ~ r1_orders_2('#skF_2',B_792,'#skF_3')
      | r2_orders_2('#skF_2',B_792,A_793)
      | ~ m1_subset_1(A_793,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_792,u1_struct_0('#skF_2'))
      | A_793 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_793)
      | ~ r2_hidden(A_793,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_6601])).

tff(c_6635,plain,(
    ! [B_794,A_795] :
      ( ~ r1_orders_2('#skF_2',B_794,'#skF_3')
      | r2_orders_2('#skF_2',B_794,A_795)
      | ~ m1_subset_1(B_794,u1_struct_0('#skF_2'))
      | A_795 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_795)
      | ~ r2_hidden(A_795,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_6625])).

tff(c_6644,plain,(
    ! [A_796,A_797] :
      ( ~ r1_orders_2('#skF_2',A_796,'#skF_3')
      | r2_orders_2('#skF_2',A_796,A_797)
      | A_797 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_797)
      | ~ r2_hidden(A_797,'#skF_5')
      | ~ r2_hidden(A_796,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_6635])).

tff(c_6651,plain,(
    ! [A_797] :
      ( ~ m1_subset_1(A_797,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r1_orders_2('#skF_2',A_797,'#skF_3')
      | A_797 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_797)
      | ~ r2_hidden(A_797,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6644,c_12])).

tff(c_6661,plain,(
    ! [A_798] :
      ( ~ m1_subset_1(A_798,u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2',A_798,'#skF_3')
      | A_798 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_798)
      | ~ r2_hidden(A_798,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6651])).

tff(c_6668,plain,(
    ! [A_1] :
      ( ~ r1_orders_2('#skF_2',A_1,'#skF_3')
      | A_1 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_1)
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6487,c_6661])).

tff(c_8656,plain,(
    ! [B_1071] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')),'#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1071,'#skF_3') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8646,c_6668])).

tff(c_8668,plain,(
    ! [B_1071] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1071,'#skF_3')),'#skF_5')
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1071,'#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8656])).

tff(c_11910,plain,(
    ! [B_1325] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1325,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1325,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_1325,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1325,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1325,'#skF_3') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11882,c_8668])).

tff(c_11971,plain,(
    ! [B_1327] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1327,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1327,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_1327,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_1327,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1327,'#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11910])).

tff(c_11975,plain,
    ( '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6867,c_11971])).

tff(c_11982,plain,
    ( '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6484,c_42,c_11975])).

tff(c_11983,plain,(
    '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_11982])).

tff(c_8611,plain,(
    ! [A_775,B_776,C_777] :
      ( r2_orders_2(A_775,'#skF_1'(k3_orders_2(A_775,B_776,C_777)),C_777)
      | ~ m1_subset_1(C_777,u1_struct_0(A_775))
      | ~ m1_subset_1(B_776,k1_zfmisc_1(u1_struct_0(A_775)))
      | ~ l1_orders_2(A_775)
      | ~ v5_orders_2(A_775)
      | ~ v4_orders_2(A_775)
      | ~ v3_orders_2(A_775)
      | v2_struct_0(A_775)
      | k3_orders_2(A_775,B_776,C_777) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6590,c_8605])).

tff(c_12125,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11983,c_8611])).

tff(c_12315,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_6484,c_46,c_12125])).

tff(c_12317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_56,c_8822,c_12315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:09:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.65  
% 9.66/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.66/3.65  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.66/3.65  
% 9.66/3.65  %Foreground sorts:
% 9.66/3.65  
% 9.66/3.65  
% 9.66/3.65  %Background operators:
% 9.66/3.65  
% 9.66/3.65  
% 9.66/3.65  %Foreground operators:
% 9.66/3.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.66/3.65  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 9.66/3.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.66/3.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.66/3.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.66/3.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.66/3.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.66/3.65  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.66/3.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.66/3.65  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 9.66/3.65  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 9.66/3.65  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 9.66/3.65  tff('#skF_5', type, '#skF_5': $i).
% 9.66/3.65  tff('#skF_2', type, '#skF_2': $i).
% 9.66/3.65  tff('#skF_3', type, '#skF_3': $i).
% 9.66/3.65  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.66/3.65  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.66/3.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.66/3.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.66/3.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.66/3.65  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 9.66/3.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.66/3.65  tff('#skF_4', type, '#skF_4': $i).
% 9.66/3.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.66/3.65  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 9.66/3.65  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 9.66/3.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.66/3.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.66/3.65  
% 9.91/3.68  tff(f_219, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 9.91/3.68  tff(f_99, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 9.91/3.68  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.91/3.68  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 9.91/3.68  tff(f_194, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 9.91/3.68  tff(f_114, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.91/3.68  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 9.91/3.68  tff(f_139, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 9.91/3.68  tff(f_79, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 9.91/3.68  tff(f_165, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 9.91/3.68  tff(c_38, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_48, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_54, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_52, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_50, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_44, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_42, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_6478, plain, (![C_755, A_756, B_757]: (m1_subset_1(C_755, k1_zfmisc_1(u1_struct_0(A_756))) | ~m2_orders_2(C_755, A_756, B_757) | ~m1_orders_1(B_757, k1_orders_1(u1_struct_0(A_756))) | ~l1_orders_2(A_756) | ~v5_orders_2(A_756) | ~v4_orders_2(A_756) | ~v3_orders_2(A_756) | v2_struct_0(A_756))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.91/3.68  tff(c_6480, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_6478])).
% 9.91/3.68  tff(c_6483, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_44, c_6480])).
% 9.91/3.68  tff(c_6484, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_6483])).
% 9.91/3.68  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.68  tff(c_6487, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_6484, c_2])).
% 9.91/3.68  tff(c_40, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.91/3.68  tff(c_4, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.91/3.68  tff(c_6826, plain, (![A_838, D_839, B_840, E_841]: (r3_orders_2(A_838, k1_funct_1(D_839, u1_struct_0(A_838)), B_840) | ~r2_hidden(B_840, E_841) | ~m2_orders_2(E_841, A_838, D_839) | ~m1_orders_1(D_839, k1_orders_1(u1_struct_0(A_838))) | ~m1_subset_1(k1_funct_1(D_839, u1_struct_0(A_838)), u1_struct_0(A_838)) | ~m1_subset_1(B_840, u1_struct_0(A_838)) | ~l1_orders_2(A_838) | ~v5_orders_2(A_838) | ~v4_orders_2(A_838) | ~v3_orders_2(A_838) | v2_struct_0(A_838))), inference(cnfTransformation, [status(thm)], [f_194])).
% 9.91/3.68  tff(c_8729, plain, (![A_1082, D_1083, A_1084]: (r3_orders_2(A_1082, k1_funct_1(D_1083, u1_struct_0(A_1082)), '#skF_1'(A_1084)) | ~m2_orders_2(A_1084, A_1082, D_1083) | ~m1_orders_1(D_1083, k1_orders_1(u1_struct_0(A_1082))) | ~m1_subset_1(k1_funct_1(D_1083, u1_struct_0(A_1082)), u1_struct_0(A_1082)) | ~m1_subset_1('#skF_1'(A_1084), u1_struct_0(A_1082)) | ~l1_orders_2(A_1082) | ~v5_orders_2(A_1082) | ~v4_orders_2(A_1082) | ~v3_orders_2(A_1082) | v2_struct_0(A_1082) | k1_xboole_0=A_1084)), inference(resolution, [status(thm)], [c_4, c_6826])).
% 9.91/3.68  tff(c_8734, plain, (![A_1084]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1084)) | ~m2_orders_2(A_1084, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1084), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=A_1084)), inference(superposition, [status(thm), theory('equality')], [c_40, c_8729])).
% 9.91/3.68  tff(c_8737, plain, (![A_1084]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1084)) | ~m2_orders_2(A_1084, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_1084), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=A_1084)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_40, c_44, c_8734])).
% 9.91/3.68  tff(c_8739, plain, (![A_1085]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1085)) | ~m2_orders_2(A_1085, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_1085), u1_struct_0('#skF_2')) | k1_xboole_0=A_1085)), inference(negUnitSimplification, [status(thm)], [c_56, c_8737])).
% 9.91/3.68  tff(c_8752, plain, (![A_1086]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1086)) | ~m2_orders_2(A_1086, '#skF_2', '#skF_4') | k1_xboole_0=A_1086 | ~r2_hidden('#skF_1'(A_1086), '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_8739])).
% 9.91/3.68  tff(c_24, plain, (![A_28, B_29, C_30]: (r1_orders_2(A_28, B_29, C_30) | ~r3_orders_2(A_28, B_29, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_28)) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | ~v3_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.91/3.68  tff(c_8754, plain, (![A_1086]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1086)) | ~m1_subset_1('#skF_1'(A_1086), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(A_1086, '#skF_2', '#skF_4') | k1_xboole_0=A_1086 | ~r2_hidden('#skF_1'(A_1086), '#skF_5'))), inference(resolution, [status(thm)], [c_8752, c_24])).
% 9.91/3.68  tff(c_8757, plain, (![A_1086]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1086)) | ~m1_subset_1('#skF_1'(A_1086), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(A_1086, '#skF_2', '#skF_4') | k1_xboole_0=A_1086 | ~r2_hidden('#skF_1'(A_1086), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_8754])).
% 9.91/3.68  tff(c_8759, plain, (![A_1087]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1087)) | ~m1_subset_1('#skF_1'(A_1087), u1_struct_0('#skF_2')) | ~m2_orders_2(A_1087, '#skF_2', '#skF_4') | k1_xboole_0=A_1087 | ~r2_hidden('#skF_1'(A_1087), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_8757])).
% 9.91/3.68  tff(c_8779, plain, (![A_1090]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_1090)) | ~m2_orders_2(A_1090, '#skF_2', '#skF_4') | k1_xboole_0=A_1090 | ~r2_hidden('#skF_1'(A_1090), '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_8759])).
% 9.91/3.68  tff(c_6488, plain, (![A_758]: (m1_subset_1(A_758, u1_struct_0('#skF_2')) | ~r2_hidden(A_758, '#skF_5'))), inference(resolution, [status(thm)], [c_6484, c_2])).
% 9.91/3.68  tff(c_75, plain, (![A_122, B_123, C_124]: (r2_orders_2(A_122, B_123, C_124) | C_124=B_123 | ~r1_orders_2(A_122, B_123, C_124) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_77, plain, (![B_123]: (r2_orders_2('#skF_2', B_123, '#skF_3') | B_123='#skF_3' | ~r1_orders_2('#skF_2', B_123, '#skF_3') | ~m1_subset_1(B_123, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_75])).
% 9.91/3.68  tff(c_80, plain, (![B_123]: (r2_orders_2('#skF_2', B_123, '#skF_3') | B_123='#skF_3' | ~r1_orders_2('#skF_2', B_123, '#skF_3') | ~m1_subset_1(B_123, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_77])).
% 9.91/3.68  tff(c_6504, plain, (![A_758]: (r2_orders_2('#skF_2', A_758, '#skF_3') | A_758='#skF_3' | ~r1_orders_2('#skF_2', A_758, '#skF_3') | ~r2_hidden(A_758, '#skF_5'))), inference(resolution, [status(thm)], [c_6488, c_80])).
% 9.91/3.68  tff(c_6597, plain, (![A_782, C_783, D_784, B_785]: (~r2_orders_2(A_782, C_783, D_784) | ~r1_orders_2(A_782, B_785, C_783) | r2_orders_2(A_782, B_785, D_784) | ~m1_subset_1(D_784, u1_struct_0(A_782)) | ~m1_subset_1(C_783, u1_struct_0(A_782)) | ~m1_subset_1(B_785, u1_struct_0(A_782)) | ~l1_orders_2(A_782) | ~v5_orders_2(A_782) | ~v4_orders_2(A_782))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.68  tff(c_6603, plain, (![B_785, A_758]: (~r1_orders_2('#skF_2', B_785, A_758) | r2_orders_2('#skF_2', B_785, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(A_758, u1_struct_0('#skF_2')) | ~m1_subset_1(B_785, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_758='#skF_3' | ~r1_orders_2('#skF_2', A_758, '#skF_3') | ~r2_hidden(A_758, '#skF_5'))), inference(resolution, [status(thm)], [c_6504, c_6597])).
% 9.91/3.68  tff(c_6612, plain, (![B_785, A_758]: (~r1_orders_2('#skF_2', B_785, A_758) | r2_orders_2('#skF_2', B_785, '#skF_3') | ~m1_subset_1(A_758, u1_struct_0('#skF_2')) | ~m1_subset_1(B_785, u1_struct_0('#skF_2')) | A_758='#skF_3' | ~r1_orders_2('#skF_2', A_758, '#skF_3') | ~r2_hidden(A_758, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_6603])).
% 9.91/3.68  tff(c_8788, plain, (![A_1090]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_1090), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | '#skF_1'(A_1090)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_1090), '#skF_3') | ~m2_orders_2(A_1090, '#skF_2', '#skF_4') | k1_xboole_0=A_1090 | ~r2_hidden('#skF_1'(A_1090), '#skF_5'))), inference(resolution, [status(thm)], [c_8779, c_6612])).
% 9.91/3.68  tff(c_8800, plain, (![A_1090]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_1090), u1_struct_0('#skF_2')) | '#skF_1'(A_1090)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_1090), '#skF_3') | ~m2_orders_2(A_1090, '#skF_2', '#skF_4') | k1_xboole_0=A_1090 | ~r2_hidden('#skF_1'(A_1090), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8788])).
% 9.91/3.68  tff(c_8804, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_8800])).
% 9.91/3.68  tff(c_12, plain, (![A_14, C_20]: (~r2_orders_2(A_14, C_20, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_8810, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_8804, c_12])).
% 9.91/3.68  tff(c_8820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_8810])).
% 9.91/3.68  tff(c_8822, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_8800])).
% 9.91/3.68  tff(c_6535, plain, (![A_763, B_764, C_765]: (m1_subset_1(k3_orders_2(A_763, B_764, C_765), k1_zfmisc_1(u1_struct_0(A_763))) | ~m1_subset_1(C_765, u1_struct_0(A_763)) | ~m1_subset_1(B_764, k1_zfmisc_1(u1_struct_0(A_763))) | ~l1_orders_2(A_763) | ~v5_orders_2(A_763) | ~v4_orders_2(A_763) | ~v3_orders_2(A_763) | v2_struct_0(A_763))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.91/3.68  tff(c_6586, plain, (![A_774, A_775, B_776, C_777]: (m1_subset_1(A_774, u1_struct_0(A_775)) | ~r2_hidden(A_774, k3_orders_2(A_775, B_776, C_777)) | ~m1_subset_1(C_777, u1_struct_0(A_775)) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_775))) | ~l1_orders_2(A_775) | ~v5_orders_2(A_775) | ~v4_orders_2(A_775) | ~v3_orders_2(A_775) | v2_struct_0(A_775))), inference(resolution, [status(thm)], [c_6535, c_2])).
% 9.91/3.68  tff(c_6590, plain, (![A_775, B_776, C_777]: (m1_subset_1('#skF_1'(k3_orders_2(A_775, B_776, C_777)), u1_struct_0(A_775)) | ~m1_subset_1(C_777, u1_struct_0(A_775)) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_775))) | ~l1_orders_2(A_775) | ~v5_orders_2(A_775) | ~v4_orders_2(A_775) | ~v3_orders_2(A_775) | v2_struct_0(A_775) | k3_orders_2(A_775, B_776, C_777)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6586])).
% 9.91/3.68  tff(c_6620, plain, (![B_788, D_789, A_790, C_791]: (r2_hidden(B_788, D_789) | ~r2_hidden(B_788, k3_orders_2(A_790, D_789, C_791)) | ~m1_subset_1(D_789, k1_zfmisc_1(u1_struct_0(A_790))) | ~m1_subset_1(C_791, u1_struct_0(A_790)) | ~m1_subset_1(B_788, u1_struct_0(A_790)) | ~l1_orders_2(A_790) | ~v5_orders_2(A_790) | ~v4_orders_2(A_790) | ~v3_orders_2(A_790) | v2_struct_0(A_790))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.91/3.68  tff(c_6833, plain, (![A_842, D_843, C_844]: (r2_hidden('#skF_1'(k3_orders_2(A_842, D_843, C_844)), D_843) | ~m1_subset_1(D_843, k1_zfmisc_1(u1_struct_0(A_842))) | ~m1_subset_1(C_844, u1_struct_0(A_842)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_842, D_843, C_844)), u1_struct_0(A_842)) | ~l1_orders_2(A_842) | ~v5_orders_2(A_842) | ~v4_orders_2(A_842) | ~v3_orders_2(A_842) | v2_struct_0(A_842) | k3_orders_2(A_842, D_843, C_844)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6620])).
% 9.91/3.68  tff(c_6845, plain, (![A_847, B_848, C_849]: (r2_hidden('#skF_1'(k3_orders_2(A_847, B_848, C_849)), B_848) | ~m1_subset_1(C_849, u1_struct_0(A_847)) | ~m1_subset_1(B_848, k1_zfmisc_1(u1_struct_0(A_847))) | ~l1_orders_2(A_847) | ~v5_orders_2(A_847) | ~v4_orders_2(A_847) | ~v3_orders_2(A_847) | v2_struct_0(A_847) | k3_orders_2(A_847, B_848, C_849)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6590, c_6833])).
% 9.91/3.68  tff(c_6838, plain, (![D_843, C_844]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), D_843) | ~m1_subset_1(D_843, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_844, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_843, C_844)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_6833])).
% 9.91/3.68  tff(c_6842, plain, (![D_843, C_844]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), D_843) | ~m1_subset_1(D_843, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_844, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_843, C_844)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_6838])).
% 9.91/3.68  tff(c_6843, plain, (![D_843, C_844]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), D_843) | ~m1_subset_1(D_843, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_844, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_843, C_844)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_843, C_844)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_6842])).
% 9.91/3.68  tff(c_6848, plain, (![C_849]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_849)), '#skF_5') | ~m1_subset_1(C_849, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_849)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6845, c_6843])).
% 9.91/3.68  tff(c_6866, plain, (![C_849]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_849)), '#skF_5') | ~m1_subset_1(C_849, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_849)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_6484, c_6848])).
% 9.91/3.68  tff(c_6867, plain, (![C_849]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_849)), '#skF_5') | ~m1_subset_1(C_849, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_849)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_6866])).
% 9.91/3.68  tff(c_36, plain, (![A_61, D_89, B_77, E_91]: (r3_orders_2(A_61, k1_funct_1(D_89, u1_struct_0(A_61)), B_77) | ~r2_hidden(B_77, E_91) | ~m2_orders_2(E_91, A_61, D_89) | ~m1_orders_1(D_89, k1_orders_1(u1_struct_0(A_61))) | ~m1_subset_1(k1_funct_1(D_89, u1_struct_0(A_61)), u1_struct_0(A_61)) | ~m1_subset_1(B_77, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_194])).
% 9.91/3.68  tff(c_11823, plain, (![B_1313, D_1314, A_1316, A_1317, C_1315]: (r3_orders_2(A_1316, k1_funct_1(D_1314, u1_struct_0(A_1316)), '#skF_1'(k3_orders_2(A_1317, B_1313, C_1315))) | ~m2_orders_2(B_1313, A_1316, D_1314) | ~m1_orders_1(D_1314, k1_orders_1(u1_struct_0(A_1316))) | ~m1_subset_1(k1_funct_1(D_1314, u1_struct_0(A_1316)), u1_struct_0(A_1316)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1317, B_1313, C_1315)), u1_struct_0(A_1316)) | ~l1_orders_2(A_1316) | ~v5_orders_2(A_1316) | ~v4_orders_2(A_1316) | ~v3_orders_2(A_1316) | v2_struct_0(A_1316) | ~m1_subset_1(C_1315, u1_struct_0(A_1317)) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1317))) | ~l1_orders_2(A_1317) | ~v5_orders_2(A_1317) | ~v4_orders_2(A_1317) | ~v3_orders_2(A_1317) | v2_struct_0(A_1317) | k3_orders_2(A_1317, B_1313, C_1315)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6845, c_36])).
% 9.91/3.68  tff(c_11828, plain, (![A_1317, B_1313, C_1315]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1317, B_1313, C_1315))) | ~m2_orders_2(B_1313, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1317, B_1313, C_1315)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_1315, u1_struct_0(A_1317)) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1317))) | ~l1_orders_2(A_1317) | ~v5_orders_2(A_1317) | ~v4_orders_2(A_1317) | ~v3_orders_2(A_1317) | v2_struct_0(A_1317) | k3_orders_2(A_1317, B_1313, C_1315)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_11823])).
% 9.91/3.68  tff(c_11831, plain, (![A_1317, B_1313, C_1315]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1317, B_1313, C_1315))) | ~m2_orders_2(B_1313, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(k3_orders_2(A_1317, B_1313, C_1315)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_1315, u1_struct_0(A_1317)) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1317))) | ~l1_orders_2(A_1317) | ~v5_orders_2(A_1317) | ~v4_orders_2(A_1317) | ~v3_orders_2(A_1317) | v2_struct_0(A_1317) | k3_orders_2(A_1317, B_1313, C_1315)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_40, c_44, c_11828])).
% 9.91/3.68  tff(c_11833, plain, (![A_1318, B_1319, C_1320]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1318, B_1319, C_1320))) | ~m2_orders_2(B_1319, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(k3_orders_2(A_1318, B_1319, C_1320)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1320, u1_struct_0(A_1318)) | ~m1_subset_1(B_1319, k1_zfmisc_1(u1_struct_0(A_1318))) | ~l1_orders_2(A_1318) | ~v5_orders_2(A_1318) | ~v4_orders_2(A_1318) | ~v3_orders_2(A_1318) | v2_struct_0(A_1318) | k3_orders_2(A_1318, B_1319, C_1320)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_11831])).
% 9.91/3.68  tff(c_11841, plain, (![B_776, C_777]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777))) | ~m2_orders_2(B_776, '#skF_2', '#skF_4') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6590, c_11833])).
% 9.91/3.68  tff(c_11851, plain, (![B_776, C_777]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777))) | ~m2_orders_2(B_776, '#skF_2', '#skF_4') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_11841])).
% 9.91/3.68  tff(c_11854, plain, (![B_1321, C_1322]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1321, C_1322))) | ~m2_orders_2(B_1321, '#skF_2', '#skF_4') | ~m1_subset_1(C_1322, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1321, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1321, C_1322)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_11851])).
% 9.91/3.68  tff(c_11856, plain, (![B_1321, C_1322]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1321, C_1322))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1321, C_1322)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_1321, '#skF_2', '#skF_4') | ~m1_subset_1(C_1322, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1321, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1321, C_1322)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11854, c_24])).
% 9.91/3.68  tff(c_11859, plain, (![B_1321, C_1322]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1321, C_1322))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1321, C_1322)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_1321, '#skF_2', '#skF_4') | ~m1_subset_1(C_1322, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1321, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1321, C_1322)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_11856])).
% 9.91/3.68  tff(c_11861, plain, (![B_1323, C_1324]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1323, C_1324))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1323, C_1324)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_1323, '#skF_2', '#skF_4') | ~m1_subset_1(C_1324, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1323, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1323, C_1324)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_11859])).
% 9.91/3.68  tff(c_11869, plain, (![B_776, C_777]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777))) | ~m2_orders_2(B_776, '#skF_2', '#skF_4') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6590, c_11861])).
% 9.91/3.68  tff(c_11879, plain, (![B_776, C_777]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777))) | ~m2_orders_2(B_776, '#skF_2', '#skF_4') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_11869])).
% 9.91/3.68  tff(c_11882, plain, (![B_1325, C_1326]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1325, C_1326))) | ~m2_orders_2(B_1325, '#skF_2', '#skF_4') | ~m1_subset_1(C_1326, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1325, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1325, C_1326)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_11879])).
% 9.91/3.68  tff(c_6747, plain, (![A_809, B_810, C_811, D_812]: (r2_orders_2(A_809, B_810, C_811) | ~r2_hidden(B_810, k3_orders_2(A_809, D_812, C_811)) | ~m1_subset_1(D_812, k1_zfmisc_1(u1_struct_0(A_809))) | ~m1_subset_1(C_811, u1_struct_0(A_809)) | ~m1_subset_1(B_810, u1_struct_0(A_809)) | ~l1_orders_2(A_809) | ~v5_orders_2(A_809) | ~v4_orders_2(A_809) | ~v3_orders_2(A_809) | v2_struct_0(A_809))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.91/3.68  tff(c_8605, plain, (![A_1061, D_1062, C_1063]: (r2_orders_2(A_1061, '#skF_1'(k3_orders_2(A_1061, D_1062, C_1063)), C_1063) | ~m1_subset_1(D_1062, k1_zfmisc_1(u1_struct_0(A_1061))) | ~m1_subset_1(C_1063, u1_struct_0(A_1061)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1061, D_1062, C_1063)), u1_struct_0(A_1061)) | ~l1_orders_2(A_1061) | ~v5_orders_2(A_1061) | ~v4_orders_2(A_1061) | ~v3_orders_2(A_1061) | v2_struct_0(A_1061) | k3_orders_2(A_1061, D_1062, C_1063)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6747])).
% 9.91/3.68  tff(c_8610, plain, (![D_1062, C_1063]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_1062, C_1063)), C_1063) | ~m1_subset_1(D_1062, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1063, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_1062, C_1063)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1062, C_1063)), '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_8605])).
% 9.91/3.68  tff(c_8614, plain, (![D_1062, C_1063]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_1062, C_1063)), C_1063) | ~m1_subset_1(D_1062, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1063, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_1062, C_1063)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1062, C_1063)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_8610])).
% 9.91/3.68  tff(c_8616, plain, (![D_1064, C_1065]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_1064, C_1065)), C_1065) | ~m1_subset_1(D_1064, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1065, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_1064, C_1065)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1064, C_1065)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_8614])).
% 9.91/3.68  tff(c_14, plain, (![A_14, B_18, C_20]: (r1_orders_2(A_14, B_18, C_20) | ~r2_orders_2(A_14, B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~m1_subset_1(B_18, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_8620, plain, (![D_1064, C_1065]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_1064, C_1065)), C_1065) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_1064, C_1065)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~m1_subset_1(D_1064, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1065, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_1064, C_1065)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1064, C_1065)), '#skF_5'))), inference(resolution, [status(thm)], [c_8616, c_14])).
% 9.91/3.68  tff(c_8634, plain, (![D_1069, C_1070]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_1069, C_1070)), C_1070) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_1069, C_1070)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_1069, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1070, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_1069, C_1070)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_1069, C_1070)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8620])).
% 9.91/3.68  tff(c_8637, plain, (![B_776, C_777]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777)), C_777) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_776, C_777)), '#skF_5') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6590, c_8634])).
% 9.91/3.68  tff(c_8643, plain, (![B_776, C_777]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_776, C_777)), C_777) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_776, C_777)), '#skF_5') | ~m1_subset_1(C_777, u1_struct_0('#skF_2')) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_776, C_777)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_8637])).
% 9.91/3.68  tff(c_8646, plain, (![B_1071, C_1072]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_1071, C_1072)), C_1072) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1071, C_1072)), '#skF_5') | ~m1_subset_1(C_1072, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1071, C_1072)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56, c_8643])).
% 9.91/3.68  tff(c_10, plain, (![A_14, B_18, C_20]: (r2_orders_2(A_14, B_18, C_20) | C_20=B_18 | ~r1_orders_2(A_14, B_18, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~m1_subset_1(B_18, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_6498, plain, (![B_18, A_758]: (r2_orders_2('#skF_2', B_18, A_758) | B_18=A_758 | ~r1_orders_2('#skF_2', B_18, A_758) | ~m1_subset_1(B_18, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden(A_758, '#skF_5'))), inference(resolution, [status(thm)], [c_6488, c_10])).
% 9.91/3.68  tff(c_6553, plain, (![B_769, A_770]: (r2_orders_2('#skF_2', B_769, A_770) | B_769=A_770 | ~r1_orders_2('#skF_2', B_769, A_770) | ~m1_subset_1(B_769, u1_struct_0('#skF_2')) | ~r2_hidden(A_770, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6498])).
% 9.91/3.68  tff(c_6559, plain, (![A_770]: (r2_orders_2('#skF_2', '#skF_3', A_770) | A_770='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_770) | ~r2_hidden(A_770, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_6553])).
% 9.91/3.68  tff(c_6601, plain, (![B_785, A_770]: (~r1_orders_2('#skF_2', B_785, '#skF_3') | r2_orders_2('#skF_2', B_785, A_770) | ~m1_subset_1(A_770, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_785, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_770='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_770) | ~r2_hidden(A_770, '#skF_5'))), inference(resolution, [status(thm)], [c_6559, c_6597])).
% 9.91/3.68  tff(c_6625, plain, (![B_792, A_793]: (~r1_orders_2('#skF_2', B_792, '#skF_3') | r2_orders_2('#skF_2', B_792, A_793) | ~m1_subset_1(A_793, u1_struct_0('#skF_2')) | ~m1_subset_1(B_792, u1_struct_0('#skF_2')) | A_793='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_793) | ~r2_hidden(A_793, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_6601])).
% 9.91/3.68  tff(c_6635, plain, (![B_794, A_795]: (~r1_orders_2('#skF_2', B_794, '#skF_3') | r2_orders_2('#skF_2', B_794, A_795) | ~m1_subset_1(B_794, u1_struct_0('#skF_2')) | A_795='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_795) | ~r2_hidden(A_795, '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_6625])).
% 9.91/3.68  tff(c_6644, plain, (![A_796, A_797]: (~r1_orders_2('#skF_2', A_796, '#skF_3') | r2_orders_2('#skF_2', A_796, A_797) | A_797='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_797) | ~r2_hidden(A_797, '#skF_5') | ~r2_hidden(A_796, '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_6635])).
% 9.91/3.68  tff(c_6651, plain, (![A_797]: (~m1_subset_1(A_797, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r1_orders_2('#skF_2', A_797, '#skF_3') | A_797='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_797) | ~r2_hidden(A_797, '#skF_5'))), inference(resolution, [status(thm)], [c_6644, c_12])).
% 9.91/3.68  tff(c_6661, plain, (![A_798]: (~m1_subset_1(A_798, u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', A_798, '#skF_3') | A_798='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_798) | ~r2_hidden(A_798, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6651])).
% 9.91/3.68  tff(c_6668, plain, (![A_1]: (~r1_orders_2('#skF_2', A_1, '#skF_3') | A_1='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_1) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_6487, c_6661])).
% 9.91/3.68  tff(c_8656, plain, (![B_1071]: ('#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1071, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_8646, c_6668])).
% 9.91/3.68  tff(c_8668, plain, (![B_1071]: ('#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1071, '#skF_3')), '#skF_5') | ~m1_subset_1(B_1071, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1071, '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8656])).
% 9.91/3.68  tff(c_11910, plain, (![B_1325]: ('#skF_1'(k3_orders_2('#skF_2', B_1325, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1325, '#skF_3')), '#skF_5') | ~m2_orders_2(B_1325, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_1325, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1325, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_11882, c_8668])).
% 9.91/3.68  tff(c_11971, plain, (![B_1327]: ('#skF_1'(k3_orders_2('#skF_2', B_1327, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1327, '#skF_3')), '#skF_5') | ~m2_orders_2(B_1327, '#skF_2', '#skF_4') | ~m1_subset_1(B_1327, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1327, '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_11910])).
% 9.91/3.68  tff(c_11975, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6867, c_11971])).
% 9.91/3.68  tff(c_11982, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6484, c_42, c_11975])).
% 9.91/3.68  tff(c_11983, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_11982])).
% 9.91/3.68  tff(c_8611, plain, (![A_775, B_776, C_777]: (r2_orders_2(A_775, '#skF_1'(k3_orders_2(A_775, B_776, C_777)), C_777) | ~m1_subset_1(C_777, u1_struct_0(A_775)) | ~m1_subset_1(B_776, k1_zfmisc_1(u1_struct_0(A_775))) | ~l1_orders_2(A_775) | ~v5_orders_2(A_775) | ~v4_orders_2(A_775) | ~v3_orders_2(A_775) | v2_struct_0(A_775) | k3_orders_2(A_775, B_776, C_777)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6590, c_8605])).
% 9.91/3.68  tff(c_12125, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11983, c_8611])).
% 9.91/3.68  tff(c_12315, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_6484, c_46, c_12125])).
% 9.91/3.68  tff(c_12317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_56, c_8822, c_12315])).
% 9.91/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.68  
% 9.91/3.68  Inference rules
% 9.91/3.68  ----------------------
% 9.91/3.68  #Ref     : 0
% 9.91/3.68  #Sup     : 2315
% 9.91/3.68  #Fact    : 0
% 9.91/3.68  #Define  : 0
% 9.91/3.68  #Split   : 23
% 9.91/3.68  #Chain   : 0
% 9.91/3.68  #Close   : 0
% 9.91/3.68  
% 9.91/3.68  Ordering : KBO
% 9.91/3.68  
% 9.91/3.68  Simplification rules
% 9.91/3.68  ----------------------
% 9.91/3.68  #Subsume      : 985
% 9.91/3.68  #Demod        : 3915
% 9.91/3.68  #Tautology    : 222
% 9.91/3.68  #SimpNegUnit  : 647
% 9.91/3.68  #BackRed      : 51
% 9.91/3.68  
% 9.91/3.68  #Partial instantiations: 0
% 9.91/3.68  #Strategies tried      : 1
% 9.91/3.68  
% 9.91/3.68  Timing (in seconds)
% 9.91/3.68  ----------------------
% 9.91/3.68  Preprocessing        : 0.34
% 9.91/3.68  Parsing              : 0.19
% 9.91/3.68  CNF conversion       : 0.03
% 9.91/3.68  Main loop            : 2.55
% 9.91/3.68  Inferencing          : 0.82
% 9.91/3.68  Reduction            : 0.75
% 9.91/3.68  Demodulation         : 0.50
% 9.91/3.68  BG Simplification    : 0.07
% 9.91/3.68  Subsumption          : 0.78
% 9.91/3.68  Abstraction          : 0.12
% 9.91/3.68  MUC search           : 0.00
% 9.91/3.68  Cooper               : 0.00
% 9.91/3.68  Total                : 2.94
% 9.91/3.68  Index Insertion      : 0.00
% 9.91/3.68  Index Deletion       : 0.00
% 9.91/3.68  Index Matching       : 0.00
% 9.91/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
