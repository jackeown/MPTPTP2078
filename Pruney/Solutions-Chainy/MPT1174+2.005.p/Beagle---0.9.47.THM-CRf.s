%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 10.88s
% Output     : CNFRefutation 11.11s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 751 expanded)
%              Number of leaves         :   37 ( 309 expanded)
%              Depth                    :   25
%              Number of atoms          :  687 (4055 expanded)
%              Number of equality atoms :   85 ( 568 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_211,negated_conjecture,(
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

tff(f_91,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_186,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_54,axiom,(
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

tff(f_131,axiom,(
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

tff(f_71,axiom,(
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

tff(f_157,axiom,(
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

tff(c_34,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_44,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_40,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_38,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_8710,plain,(
    ! [C_830,A_831,B_832] :
      ( m1_subset_1(C_830,k1_zfmisc_1(u1_struct_0(A_831)))
      | ~ m2_orders_2(C_830,A_831,B_832)
      | ~ m1_orders_1(B_832,k1_orders_1(u1_struct_0(A_831)))
      | ~ l1_orders_2(A_831)
      | ~ v5_orders_2(A_831)
      | ~ v4_orders_2(A_831)
      | ~ v3_orders_2(A_831)
      | v2_struct_0(A_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8712,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_8710])).

tff(c_8715,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_40,c_8712])).

tff(c_8716,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_8715])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8719,plain,(
    ! [A_3] :
      ( m1_subset_1(A_3,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_3,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8716,c_4])).

tff(c_36,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9050,plain,(
    ! [A_907,D_908,B_909,E_910] :
      ( r3_orders_2(A_907,k1_funct_1(D_908,u1_struct_0(A_907)),B_909)
      | ~ r2_hidden(B_909,E_910)
      | ~ m2_orders_2(E_910,A_907,D_908)
      | ~ m1_orders_1(D_908,k1_orders_1(u1_struct_0(A_907)))
      | ~ m1_subset_1(k1_funct_1(D_908,u1_struct_0(A_907)),u1_struct_0(A_907))
      | ~ m1_subset_1(B_909,u1_struct_0(A_907))
      | ~ l1_orders_2(A_907)
      | ~ v5_orders_2(A_907)
      | ~ v4_orders_2(A_907)
      | ~ v3_orders_2(A_907)
      | v2_struct_0(A_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_9165,plain,(
    ! [A_934,D_935,A_936] :
      ( r3_orders_2(A_934,k1_funct_1(D_935,u1_struct_0(A_934)),'#skF_1'(A_936))
      | ~ m2_orders_2(A_936,A_934,D_935)
      | ~ m1_orders_1(D_935,k1_orders_1(u1_struct_0(A_934)))
      | ~ m1_subset_1(k1_funct_1(D_935,u1_struct_0(A_934)),u1_struct_0(A_934))
      | ~ m1_subset_1('#skF_1'(A_936),u1_struct_0(A_934))
      | ~ l1_orders_2(A_934)
      | ~ v5_orders_2(A_934)
      | ~ v4_orders_2(A_934)
      | ~ v3_orders_2(A_934)
      | v2_struct_0(A_934)
      | k1_xboole_0 = A_936 ) ),
    inference(resolution,[status(thm)],[c_2,c_9050])).

tff(c_9170,plain,(
    ! [A_936] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_936))
      | ~ m2_orders_2(A_936,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_936),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = A_936 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9165])).

tff(c_9173,plain,(
    ! [A_936] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_936))
      | ~ m2_orders_2(A_936,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_936),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = A_936 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_36,c_40,c_9170])).

tff(c_9175,plain,(
    ! [A_937] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_937))
      | ~ m2_orders_2(A_937,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_937),u1_struct_0('#skF_2'))
      | k1_xboole_0 = A_937 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9173])).

tff(c_9188,plain,(
    ! [A_938] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_938))
      | ~ m2_orders_2(A_938,'#skF_2','#skF_4')
      | k1_xboole_0 = A_938
      | ~ r2_hidden('#skF_1'(A_938),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_9175])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_orders_2(A_20,B_21,C_22)
      | ~ r3_orders_2(A_20,B_21,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_20))
      | ~ m1_subset_1(B_21,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_9190,plain,(
    ! [A_938] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_938))
      | ~ m1_subset_1('#skF_1'(A_938),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(A_938,'#skF_2','#skF_4')
      | k1_xboole_0 = A_938
      | ~ r2_hidden('#skF_1'(A_938),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9188,c_20])).

tff(c_9193,plain,(
    ! [A_938] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_938))
      | ~ m1_subset_1('#skF_1'(A_938),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(A_938,'#skF_2','#skF_4')
      | k1_xboole_0 = A_938
      | ~ r2_hidden('#skF_1'(A_938),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_9190])).

tff(c_9195,plain,(
    ! [A_939] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_939))
      | ~ m1_subset_1('#skF_1'(A_939),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(A_939,'#skF_2','#skF_4')
      | k1_xboole_0 = A_939
      | ~ r2_hidden('#skF_1'(A_939),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9193])).

tff(c_9215,plain,(
    ! [A_942] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(A_942))
      | ~ m2_orders_2(A_942,'#skF_2','#skF_4')
      | k1_xboole_0 = A_942
      | ~ r2_hidden('#skF_1'(A_942),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_9195])).

tff(c_8720,plain,(
    ! [A_833] :
      ( m1_subset_1(A_833,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_833,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8716,c_4])).

tff(c_61,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_orders_2(A_104,B_105,C_106)
      | C_106 = B_105
      | ~ r1_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [B_105] :
      ( r2_orders_2('#skF_2',B_105,'#skF_3')
      | B_105 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_66,plain,(
    ! [B_105] :
      ( r2_orders_2('#skF_2',B_105,'#skF_3')
      | B_105 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_105,'#skF_3')
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_8731,plain,(
    ! [A_833] :
      ( r2_orders_2('#skF_2',A_833,'#skF_3')
      | A_833 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_833,'#skF_3')
      | ~ r2_hidden(A_833,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8720,c_66])).

tff(c_8829,plain,(
    ! [A_857,C_858,D_859,B_860] :
      ( ~ r2_orders_2(A_857,C_858,D_859)
      | ~ r1_orders_2(A_857,B_860,C_858)
      | r2_orders_2(A_857,B_860,D_859)
      | ~ m1_subset_1(D_859,u1_struct_0(A_857))
      | ~ m1_subset_1(C_858,u1_struct_0(A_857))
      | ~ m1_subset_1(B_860,u1_struct_0(A_857))
      | ~ l1_orders_2(A_857)
      | ~ v5_orders_2(A_857)
      | ~ v4_orders_2(A_857) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8835,plain,(
    ! [B_860,A_833] :
      ( ~ r1_orders_2('#skF_2',B_860,A_833)
      | r2_orders_2('#skF_2',B_860,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_833,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_860,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_833 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_833,'#skF_3')
      | ~ r2_hidden(A_833,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8731,c_8829])).

tff(c_8844,plain,(
    ! [B_860,A_833] :
      ( ~ r1_orders_2('#skF_2',B_860,A_833)
      | r2_orders_2('#skF_2',B_860,'#skF_3')
      | ~ m1_subset_1(A_833,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_860,u1_struct_0('#skF_2'))
      | A_833 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_833,'#skF_3')
      | ~ r2_hidden(A_833,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_8835])).

tff(c_9221,plain,(
    ! [A_942] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_942),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | '#skF_1'(A_942) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_942),'#skF_3')
      | ~ m2_orders_2(A_942,'#skF_2','#skF_4')
      | k1_xboole_0 = A_942
      | ~ r2_hidden('#skF_1'(A_942),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9215,c_8844])).

tff(c_9232,plain,(
    ! [A_942] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1('#skF_1'(A_942),u1_struct_0('#skF_2'))
      | '#skF_1'(A_942) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(A_942),'#skF_3')
      | ~ m2_orders_2(A_942,'#skF_2','#skF_4')
      | k1_xboole_0 = A_942
      | ~ r2_hidden('#skF_1'(A_942),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_9221])).

tff(c_9236,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9232])).

tff(c_8,plain,(
    ! [A_6,C_12] :
      ( ~ r2_orders_2(A_6,C_12,C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9242,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_9236,c_8])).

tff(c_9252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_9242])).

tff(c_9254,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_9232])).

tff(c_8747,plain,(
    ! [A_835,B_836,C_837] :
      ( m1_subset_1(k3_orders_2(A_835,B_836,C_837),k1_zfmisc_1(u1_struct_0(A_835)))
      | ~ m1_subset_1(C_837,u1_struct_0(A_835))
      | ~ m1_subset_1(B_836,k1_zfmisc_1(u1_struct_0(A_835)))
      | ~ l1_orders_2(A_835)
      | ~ v5_orders_2(A_835)
      | ~ v4_orders_2(A_835)
      | ~ v3_orders_2(A_835)
      | v2_struct_0(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8818,plain,(
    ! [A_849,A_850,B_851,C_852] :
      ( m1_subset_1(A_849,u1_struct_0(A_850))
      | ~ r2_hidden(A_849,k3_orders_2(A_850,B_851,C_852))
      | ~ m1_subset_1(C_852,u1_struct_0(A_850))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0(A_850)))
      | ~ l1_orders_2(A_850)
      | ~ v5_orders_2(A_850)
      | ~ v4_orders_2(A_850)
      | ~ v3_orders_2(A_850)
      | v2_struct_0(A_850) ) ),
    inference(resolution,[status(thm)],[c_8747,c_4])).

tff(c_8822,plain,(
    ! [A_850,B_851,C_852] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_850,B_851,C_852)),u1_struct_0(A_850))
      | ~ m1_subset_1(C_852,u1_struct_0(A_850))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0(A_850)))
      | ~ l1_orders_2(A_850)
      | ~ v5_orders_2(A_850)
      | ~ v4_orders_2(A_850)
      | ~ v3_orders_2(A_850)
      | v2_struct_0(A_850)
      | k3_orders_2(A_850,B_851,C_852) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_8818])).

tff(c_8930,plain,(
    ! [B_877,D_878,A_879,C_880] :
      ( r2_hidden(B_877,D_878)
      | ~ r2_hidden(B_877,k3_orders_2(A_879,D_878,C_880))
      | ~ m1_subset_1(D_878,k1_zfmisc_1(u1_struct_0(A_879)))
      | ~ m1_subset_1(C_880,u1_struct_0(A_879))
      | ~ m1_subset_1(B_877,u1_struct_0(A_879))
      | ~ l1_orders_2(A_879)
      | ~ v5_orders_2(A_879)
      | ~ v4_orders_2(A_879)
      | ~ v3_orders_2(A_879)
      | v2_struct_0(A_879) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9057,plain,(
    ! [A_911,D_912,C_913] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_911,D_912,C_913)),D_912)
      | ~ m1_subset_1(D_912,k1_zfmisc_1(u1_struct_0(A_911)))
      | ~ m1_subset_1(C_913,u1_struct_0(A_911))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_911,D_912,C_913)),u1_struct_0(A_911))
      | ~ l1_orders_2(A_911)
      | ~ v5_orders_2(A_911)
      | ~ v4_orders_2(A_911)
      | ~ v3_orders_2(A_911)
      | v2_struct_0(A_911)
      | k3_orders_2(A_911,D_912,C_913) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_8930])).

tff(c_9069,plain,(
    ! [A_916,B_917,C_918] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_916,B_917,C_918)),B_917)
      | ~ m1_subset_1(C_918,u1_struct_0(A_916))
      | ~ m1_subset_1(B_917,k1_zfmisc_1(u1_struct_0(A_916)))
      | ~ l1_orders_2(A_916)
      | ~ v5_orders_2(A_916)
      | ~ v4_orders_2(A_916)
      | ~ v3_orders_2(A_916)
      | v2_struct_0(A_916)
      | k3_orders_2(A_916,B_917,C_918) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8822,c_9057])).

tff(c_9062,plain,(
    ! [D_912,C_913] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),D_912)
      | ~ m1_subset_1(D_912,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_913,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_912,C_913) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_9057])).

tff(c_9066,plain,(
    ! [D_912,C_913] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),D_912)
      | ~ m1_subset_1(D_912,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_913,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_912,C_913) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_9062])).

tff(c_9067,plain,(
    ! [D_912,C_913] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),D_912)
      | ~ m1_subset_1(D_912,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_913,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_912,C_913) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_912,C_913)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9066])).

tff(c_9072,plain,(
    ! [C_918] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_918)),'#skF_5')
      | ~ m1_subset_1(C_918,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_918) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9069,c_9067])).

tff(c_9086,plain,(
    ! [C_918] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_918)),'#skF_5')
      | ~ m1_subset_1(C_918,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_918) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_8716,c_9072])).

tff(c_9087,plain,(
    ! [C_918] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_918)),'#skF_5')
      | ~ m1_subset_1(C_918,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_918) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9086])).

tff(c_32,plain,(
    ! [A_53,D_81,B_69,E_83] :
      ( r3_orders_2(A_53,k1_funct_1(D_81,u1_struct_0(A_53)),B_69)
      | ~ r2_hidden(B_69,E_83)
      | ~ m2_orders_2(E_83,A_53,D_81)
      | ~ m1_orders_1(D_81,k1_orders_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(k1_funct_1(D_81,u1_struct_0(A_53)),u1_struct_0(A_53))
      | ~ m1_subset_1(B_69,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53)
      | ~ v4_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_16423,plain,(
    ! [C_1519,D_1518,A_1516,B_1520,A_1517] :
      ( r3_orders_2(A_1516,k1_funct_1(D_1518,u1_struct_0(A_1516)),'#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)))
      | ~ m2_orders_2(B_1520,A_1516,D_1518)
      | ~ m1_orders_1(D_1518,k1_orders_1(u1_struct_0(A_1516)))
      | ~ m1_subset_1(k1_funct_1(D_1518,u1_struct_0(A_1516)),u1_struct_0(A_1516))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)),u1_struct_0(A_1516))
      | ~ l1_orders_2(A_1516)
      | ~ v5_orders_2(A_1516)
      | ~ v4_orders_2(A_1516)
      | ~ v3_orders_2(A_1516)
      | v2_struct_0(A_1516)
      | ~ m1_subset_1(C_1519,u1_struct_0(A_1517))
      | ~ m1_subset_1(B_1520,k1_zfmisc_1(u1_struct_0(A_1517)))
      | ~ l1_orders_2(A_1517)
      | ~ v5_orders_2(A_1517)
      | ~ v4_orders_2(A_1517)
      | ~ v3_orders_2(A_1517)
      | v2_struct_0(A_1517)
      | k3_orders_2(A_1517,B_1520,C_1519) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9069,c_32])).

tff(c_16428,plain,(
    ! [A_1517,B_1520,C_1519] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)))
      | ~ m2_orders_2(B_1520,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1519,u1_struct_0(A_1517))
      | ~ m1_subset_1(B_1520,k1_zfmisc_1(u1_struct_0(A_1517)))
      | ~ l1_orders_2(A_1517)
      | ~ v5_orders_2(A_1517)
      | ~ v4_orders_2(A_1517)
      | ~ v3_orders_2(A_1517)
      | v2_struct_0(A_1517)
      | k3_orders_2(A_1517,B_1520,C_1519) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_16423])).

tff(c_16431,plain,(
    ! [A_1517,B_1520,C_1519] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)))
      | ~ m2_orders_2(B_1520,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1517,B_1520,C_1519)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1519,u1_struct_0(A_1517))
      | ~ m1_subset_1(B_1520,k1_zfmisc_1(u1_struct_0(A_1517)))
      | ~ l1_orders_2(A_1517)
      | ~ v5_orders_2(A_1517)
      | ~ v4_orders_2(A_1517)
      | ~ v3_orders_2(A_1517)
      | v2_struct_0(A_1517)
      | k3_orders_2(A_1517,B_1520,C_1519) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_36,c_40,c_16428])).

tff(c_16988,plain,(
    ! [A_1551,B_1552,C_1553] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2(A_1551,B_1552,C_1553)))
      | ~ m2_orders_2(B_1552,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_1551,B_1552,C_1553)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_1553,u1_struct_0(A_1551))
      | ~ m1_subset_1(B_1552,k1_zfmisc_1(u1_struct_0(A_1551)))
      | ~ l1_orders_2(A_1551)
      | ~ v5_orders_2(A_1551)
      | ~ v4_orders_2(A_1551)
      | ~ v3_orders_2(A_1551)
      | v2_struct_0(A_1551)
      | k3_orders_2(A_1551,B_1552,C_1553) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_16431])).

tff(c_16996,plain,(
    ! [B_851,C_852] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)))
      | ~ m2_orders_2(B_851,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8822,c_16988])).

tff(c_17006,plain,(
    ! [B_851,C_852] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)))
      | ~ m2_orders_2(B_851,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_16996])).

tff(c_17009,plain,(
    ! [B_1554,C_1555] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1554,C_1555)))
      | ~ m2_orders_2(B_1554,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1555,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1554,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1554,C_1555) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_17006])).

tff(c_17011,plain,(
    ! [B_1554,C_1555] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1554,C_1555)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1554,C_1555)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_1554,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1555,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1554,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1554,C_1555) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_17009,c_20])).

tff(c_17014,plain,(
    ! [B_1554,C_1555] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1554,C_1555)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1554,C_1555)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_1554,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1555,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1554,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1554,C_1555) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_17011])).

tff(c_17016,plain,(
    ! [B_1556,C_1557] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1556,C_1557)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',B_1556,C_1557)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_1556,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1557,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1556,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1556,C_1557) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_17014])).

tff(c_17024,plain,(
    ! [B_851,C_852] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)))
      | ~ m2_orders_2(B_851,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8822,c_17016])).

tff(c_17034,plain,(
    ! [B_851,C_852] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)))
      | ~ m2_orders_2(B_851,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_17024])).

tff(c_17037,plain,(
    ! [B_1558,C_1559] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_1558,C_1559)))
      | ~ m2_orders_2(B_1558,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_1559,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1558,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1558,C_1559) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_17034])).

tff(c_8999,plain,(
    ! [A_892,B_893,C_894,D_895] :
      ( r2_orders_2(A_892,B_893,C_894)
      | ~ r2_hidden(B_893,k3_orders_2(A_892,D_895,C_894))
      | ~ m1_subset_1(D_895,k1_zfmisc_1(u1_struct_0(A_892)))
      | ~ m1_subset_1(C_894,u1_struct_0(A_892))
      | ~ m1_subset_1(B_893,u1_struct_0(A_892))
      | ~ l1_orders_2(A_892)
      | ~ v5_orders_2(A_892)
      | ~ v4_orders_2(A_892)
      | ~ v3_orders_2(A_892)
      | v2_struct_0(A_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9136,plain,(
    ! [A_926,D_927,C_928] :
      ( r2_orders_2(A_926,'#skF_1'(k3_orders_2(A_926,D_927,C_928)),C_928)
      | ~ m1_subset_1(D_927,k1_zfmisc_1(u1_struct_0(A_926)))
      | ~ m1_subset_1(C_928,u1_struct_0(A_926))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_926,D_927,C_928)),u1_struct_0(A_926))
      | ~ l1_orders_2(A_926)
      | ~ v5_orders_2(A_926)
      | ~ v4_orders_2(A_926)
      | ~ v3_orders_2(A_926)
      | v2_struct_0(A_926)
      | k3_orders_2(A_926,D_927,C_928) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_8999])).

tff(c_9141,plain,(
    ! [D_927,C_928] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_927,C_928)),C_928)
      | ~ m1_subset_1(D_927,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_928,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_927,C_928) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_927,C_928)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_9136])).

tff(c_9145,plain,(
    ! [D_927,C_928] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_927,C_928)),C_928)
      | ~ m1_subset_1(D_927,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_928,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_927,C_928) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_927,C_928)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_9141])).

tff(c_9147,plain,(
    ! [D_929,C_930] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_929,C_930)),C_930)
      | ~ m1_subset_1(D_929,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_930,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_929,C_930) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_929,C_930)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9145])).

tff(c_10,plain,(
    ! [A_6,B_10,C_12] :
      ( r1_orders_2(A_6,B_10,C_12)
      | ~ r2_orders_2(A_6,B_10,C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(B_10,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9151,plain,(
    ! [D_929,C_930] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_929,C_930)),C_930)
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_929,C_930)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ m1_subset_1(D_929,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_930,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_929,C_930) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_929,C_930)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9147,c_10])).

tff(c_9596,plain,(
    ! [D_984,C_985] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_984,C_985)),C_985)
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_984,C_985)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_984,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_985,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_984,C_985) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_984,C_985)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9151])).

tff(c_9599,plain,(
    ! [B_851,C_852] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)),C_852)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_851,C_852)),'#skF_5')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8822,c_9596])).

tff(c_9605,plain,(
    ! [B_851,C_852] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_851,C_852)),C_852)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_851,C_852)),'#skF_5')
      | ~ m1_subset_1(C_852,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',B_851,C_852) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_9599])).

tff(c_9608,plain,(
    ! [B_986,C_987] :
      ( r1_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',B_986,C_987)),C_987)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_986,C_987)),'#skF_5')
      | ~ m1_subset_1(C_987,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_986,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_986,C_987) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9605])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( r2_orders_2(A_6,B_10,C_12)
      | C_12 = B_10
      | ~ r1_orders_2(A_6,B_10,C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_6))
      | ~ m1_subset_1(B_10,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8730,plain,(
    ! [B_10,A_833] :
      ( r2_orders_2('#skF_2',B_10,A_833)
      | B_10 = A_833
      | ~ r1_orders_2('#skF_2',B_10,A_833)
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r2_hidden(A_833,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8720,c_6])).

tff(c_8785,plain,(
    ! [B_844,A_845] :
      ( r2_orders_2('#skF_2',B_844,A_845)
      | B_844 = A_845
      | ~ r1_orders_2('#skF_2',B_844,A_845)
      | ~ m1_subset_1(B_844,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_845,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8730])).

tff(c_8791,plain,(
    ! [A_845] :
      ( r2_orders_2('#skF_2','#skF_3',A_845)
      | A_845 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_845)
      | ~ r2_hidden(A_845,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_8785])).

tff(c_8833,plain,(
    ! [B_860,A_845] :
      ( ~ r1_orders_2('#skF_2',B_860,'#skF_3')
      | r2_orders_2('#skF_2',B_860,A_845)
      | ~ m1_subset_1(A_845,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_860,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | A_845 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_845)
      | ~ r2_hidden(A_845,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8791,c_8829])).

tff(c_8852,plain,(
    ! [B_863,A_864] :
      ( ~ r1_orders_2('#skF_2',B_863,'#skF_3')
      | r2_orders_2('#skF_2',B_863,A_864)
      | ~ m1_subset_1(A_864,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_863,u1_struct_0('#skF_2'))
      | A_864 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_864)
      | ~ r2_hidden(A_864,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_8833])).

tff(c_8862,plain,(
    ! [B_865,A_866] :
      ( ~ r1_orders_2('#skF_2',B_865,'#skF_3')
      | r2_orders_2('#skF_2',B_865,A_866)
      | ~ m1_subset_1(B_865,u1_struct_0('#skF_2'))
      | A_866 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_866)
      | ~ r2_hidden(A_866,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_8852])).

tff(c_8871,plain,(
    ! [A_867,A_868] :
      ( ~ r1_orders_2('#skF_2',A_867,'#skF_3')
      | r2_orders_2('#skF_2',A_867,A_868)
      | A_868 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_868)
      | ~ r2_hidden(A_868,'#skF_5')
      | ~ r2_hidden(A_867,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_8862])).

tff(c_8878,plain,(
    ! [A_868] :
      ( ~ m1_subset_1(A_868,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r1_orders_2('#skF_2',A_868,'#skF_3')
      | A_868 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_868)
      | ~ r2_hidden(A_868,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8871,c_8])).

tff(c_8888,plain,(
    ! [A_869] :
      ( ~ m1_subset_1(A_869,u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2',A_869,'#skF_3')
      | A_869 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_869)
      | ~ r2_hidden(A_869,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8878])).

tff(c_8895,plain,(
    ! [A_3] :
      ( ~ r1_orders_2('#skF_2',A_3,'#skF_3')
      | A_3 = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3',A_3)
      | ~ r2_hidden(A_3,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8719,c_8888])).

tff(c_9627,plain,(
    ! [B_986] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')),'#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_986,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_986,'#skF_3') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9608,c_8895])).

tff(c_9644,plain,(
    ! [B_986] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_986,'#skF_3')),'#skF_5')
      | ~ m1_subset_1(B_986,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_986,'#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_9627])).

tff(c_17066,plain,(
    ! [B_1558] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1558,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1558,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_1558,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_1558,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1558,'#skF_3') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_17037,c_9644])).

tff(c_17132,plain,(
    ! [B_1560] :
      ( '#skF_1'(k3_orders_2('#skF_2',B_1560,'#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_1560,'#skF_3')),'#skF_5')
      | ~ m2_orders_2(B_1560,'#skF_2','#skF_4')
      | ~ m1_subset_1(B_1560,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',B_1560,'#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_17066])).

tff(c_17136,plain,
    ( '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9087,c_17132])).

tff(c_17143,plain,
    ( '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8716,c_38,c_17136])).

tff(c_17144,plain,(
    '#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_17143])).

tff(c_9142,plain,(
    ! [A_850,B_851,C_852] :
      ( r2_orders_2(A_850,'#skF_1'(k3_orders_2(A_850,B_851,C_852)),C_852)
      | ~ m1_subset_1(C_852,u1_struct_0(A_850))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0(A_850)))
      | ~ l1_orders_2(A_850)
      | ~ v5_orders_2(A_850)
      | ~ v4_orders_2(A_850)
      | ~ v3_orders_2(A_850)
      | v2_struct_0(A_850)
      | k3_orders_2(A_850,B_851,C_852) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8822,c_9136])).

tff(c_17317,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17144,c_9142])).

tff(c_17522,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_8716,c_42,c_17317])).

tff(c_17524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_52,c_9254,c_17522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.88/4.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.31  
% 10.88/4.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.88/4.32  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.88/4.32  
% 10.88/4.32  %Foreground sorts:
% 10.88/4.32  
% 10.88/4.32  
% 10.88/4.32  %Background operators:
% 10.88/4.32  
% 10.88/4.32  
% 10.88/4.32  %Foreground operators:
% 10.88/4.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.88/4.32  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 10.88/4.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.88/4.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.88/4.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.88/4.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.88/4.32  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.88/4.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.88/4.32  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 10.88/4.32  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 10.88/4.32  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 10.88/4.32  tff('#skF_5', type, '#skF_5': $i).
% 10.88/4.32  tff('#skF_2', type, '#skF_2': $i).
% 10.88/4.32  tff('#skF_3', type, '#skF_3': $i).
% 10.88/4.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.88/4.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.88/4.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.88/4.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.88/4.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.88/4.32  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 10.88/4.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.88/4.32  tff('#skF_4', type, '#skF_4': $i).
% 10.88/4.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.88/4.32  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 10.88/4.32  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 10.88/4.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.88/4.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.88/4.32  
% 11.11/4.34  tff(f_211, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 11.11/4.34  tff(f_91, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 11.11/4.34  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 11.11/4.34  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.11/4.34  tff(f_186, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 11.11/4.34  tff(f_106, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 11.11/4.34  tff(f_54, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 11.11/4.34  tff(f_131, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 11.11/4.34  tff(f_71, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 11.11/4.34  tff(f_157, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 11.11/4.34  tff(c_34, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_44, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_48, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_40, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_38, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_8710, plain, (![C_830, A_831, B_832]: (m1_subset_1(C_830, k1_zfmisc_1(u1_struct_0(A_831))) | ~m2_orders_2(C_830, A_831, B_832) | ~m1_orders_1(B_832, k1_orders_1(u1_struct_0(A_831))) | ~l1_orders_2(A_831) | ~v5_orders_2(A_831) | ~v4_orders_2(A_831) | ~v3_orders_2(A_831) | v2_struct_0(A_831))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.11/4.34  tff(c_8712, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_8710])).
% 11.11/4.34  tff(c_8715, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_40, c_8712])).
% 11.11/4.34  tff(c_8716, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_8715])).
% 11.11/4.34  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.11/4.34  tff(c_8719, plain, (![A_3]: (m1_subset_1(A_3, u1_struct_0('#skF_2')) | ~r2_hidden(A_3, '#skF_5'))), inference(resolution, [status(thm)], [c_8716, c_4])).
% 11.11/4.34  tff(c_36, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.11/4.34  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.11/4.34  tff(c_9050, plain, (![A_907, D_908, B_909, E_910]: (r3_orders_2(A_907, k1_funct_1(D_908, u1_struct_0(A_907)), B_909) | ~r2_hidden(B_909, E_910) | ~m2_orders_2(E_910, A_907, D_908) | ~m1_orders_1(D_908, k1_orders_1(u1_struct_0(A_907))) | ~m1_subset_1(k1_funct_1(D_908, u1_struct_0(A_907)), u1_struct_0(A_907)) | ~m1_subset_1(B_909, u1_struct_0(A_907)) | ~l1_orders_2(A_907) | ~v5_orders_2(A_907) | ~v4_orders_2(A_907) | ~v3_orders_2(A_907) | v2_struct_0(A_907))), inference(cnfTransformation, [status(thm)], [f_186])).
% 11.11/4.34  tff(c_9165, plain, (![A_934, D_935, A_936]: (r3_orders_2(A_934, k1_funct_1(D_935, u1_struct_0(A_934)), '#skF_1'(A_936)) | ~m2_orders_2(A_936, A_934, D_935) | ~m1_orders_1(D_935, k1_orders_1(u1_struct_0(A_934))) | ~m1_subset_1(k1_funct_1(D_935, u1_struct_0(A_934)), u1_struct_0(A_934)) | ~m1_subset_1('#skF_1'(A_936), u1_struct_0(A_934)) | ~l1_orders_2(A_934) | ~v5_orders_2(A_934) | ~v4_orders_2(A_934) | ~v3_orders_2(A_934) | v2_struct_0(A_934) | k1_xboole_0=A_936)), inference(resolution, [status(thm)], [c_2, c_9050])).
% 11.11/4.34  tff(c_9170, plain, (![A_936]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_936)) | ~m2_orders_2(A_936, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_936), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=A_936)), inference(superposition, [status(thm), theory('equality')], [c_36, c_9165])).
% 11.11/4.34  tff(c_9173, plain, (![A_936]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_936)) | ~m2_orders_2(A_936, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_936), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=A_936)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_36, c_40, c_9170])).
% 11.11/4.34  tff(c_9175, plain, (![A_937]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_937)) | ~m2_orders_2(A_937, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_937), u1_struct_0('#skF_2')) | k1_xboole_0=A_937)), inference(negUnitSimplification, [status(thm)], [c_52, c_9173])).
% 11.11/4.34  tff(c_9188, plain, (![A_938]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_938)) | ~m2_orders_2(A_938, '#skF_2', '#skF_4') | k1_xboole_0=A_938 | ~r2_hidden('#skF_1'(A_938), '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_9175])).
% 11.11/4.34  tff(c_20, plain, (![A_20, B_21, C_22]: (r1_orders_2(A_20, B_21, C_22) | ~r3_orders_2(A_20, B_21, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_20)) | ~m1_subset_1(B_21, u1_struct_0(A_20)) | ~l1_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.11/4.34  tff(c_9190, plain, (![A_938]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_938)) | ~m1_subset_1('#skF_1'(A_938), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(A_938, '#skF_2', '#skF_4') | k1_xboole_0=A_938 | ~r2_hidden('#skF_1'(A_938), '#skF_5'))), inference(resolution, [status(thm)], [c_9188, c_20])).
% 11.11/4.34  tff(c_9193, plain, (![A_938]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_938)) | ~m1_subset_1('#skF_1'(A_938), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(A_938, '#skF_2', '#skF_4') | k1_xboole_0=A_938 | ~r2_hidden('#skF_1'(A_938), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_9190])).
% 11.11/4.34  tff(c_9195, plain, (![A_939]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_939)) | ~m1_subset_1('#skF_1'(A_939), u1_struct_0('#skF_2')) | ~m2_orders_2(A_939, '#skF_2', '#skF_4') | k1_xboole_0=A_939 | ~r2_hidden('#skF_1'(A_939), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_9193])).
% 11.11/4.34  tff(c_9215, plain, (![A_942]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(A_942)) | ~m2_orders_2(A_942, '#skF_2', '#skF_4') | k1_xboole_0=A_942 | ~r2_hidden('#skF_1'(A_942), '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_9195])).
% 11.11/4.34  tff(c_8720, plain, (![A_833]: (m1_subset_1(A_833, u1_struct_0('#skF_2')) | ~r2_hidden(A_833, '#skF_5'))), inference(resolution, [status(thm)], [c_8716, c_4])).
% 11.11/4.34  tff(c_61, plain, (![A_104, B_105, C_106]: (r2_orders_2(A_104, B_105, C_106) | C_106=B_105 | ~r1_orders_2(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.11/4.34  tff(c_63, plain, (![B_105]: (r2_orders_2('#skF_2', B_105, '#skF_3') | B_105='#skF_3' | ~r1_orders_2('#skF_2', B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_61])).
% 11.11/4.34  tff(c_66, plain, (![B_105]: (r2_orders_2('#skF_2', B_105, '#skF_3') | B_105='#skF_3' | ~r1_orders_2('#skF_2', B_105, '#skF_3') | ~m1_subset_1(B_105, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 11.11/4.34  tff(c_8731, plain, (![A_833]: (r2_orders_2('#skF_2', A_833, '#skF_3') | A_833='#skF_3' | ~r1_orders_2('#skF_2', A_833, '#skF_3') | ~r2_hidden(A_833, '#skF_5'))), inference(resolution, [status(thm)], [c_8720, c_66])).
% 11.11/4.34  tff(c_8829, plain, (![A_857, C_858, D_859, B_860]: (~r2_orders_2(A_857, C_858, D_859) | ~r1_orders_2(A_857, B_860, C_858) | r2_orders_2(A_857, B_860, D_859) | ~m1_subset_1(D_859, u1_struct_0(A_857)) | ~m1_subset_1(C_858, u1_struct_0(A_857)) | ~m1_subset_1(B_860, u1_struct_0(A_857)) | ~l1_orders_2(A_857) | ~v5_orders_2(A_857) | ~v4_orders_2(A_857))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.11/4.34  tff(c_8835, plain, (![B_860, A_833]: (~r1_orders_2('#skF_2', B_860, A_833) | r2_orders_2('#skF_2', B_860, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(A_833, u1_struct_0('#skF_2')) | ~m1_subset_1(B_860, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_833='#skF_3' | ~r1_orders_2('#skF_2', A_833, '#skF_3') | ~r2_hidden(A_833, '#skF_5'))), inference(resolution, [status(thm)], [c_8731, c_8829])).
% 11.11/4.34  tff(c_8844, plain, (![B_860, A_833]: (~r1_orders_2('#skF_2', B_860, A_833) | r2_orders_2('#skF_2', B_860, '#skF_3') | ~m1_subset_1(A_833, u1_struct_0('#skF_2')) | ~m1_subset_1(B_860, u1_struct_0('#skF_2')) | A_833='#skF_3' | ~r1_orders_2('#skF_2', A_833, '#skF_3') | ~r2_hidden(A_833, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_8835])).
% 11.11/4.34  tff(c_9221, plain, (![A_942]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_942), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | '#skF_1'(A_942)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_942), '#skF_3') | ~m2_orders_2(A_942, '#skF_2', '#skF_4') | k1_xboole_0=A_942 | ~r2_hidden('#skF_1'(A_942), '#skF_5'))), inference(resolution, [status(thm)], [c_9215, c_8844])).
% 11.11/4.34  tff(c_9232, plain, (![A_942]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_1'(A_942), u1_struct_0('#skF_2')) | '#skF_1'(A_942)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(A_942), '#skF_3') | ~m2_orders_2(A_942, '#skF_2', '#skF_4') | k1_xboole_0=A_942 | ~r2_hidden('#skF_1'(A_942), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_9221])).
% 11.11/4.34  tff(c_9236, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_9232])).
% 11.11/4.34  tff(c_8, plain, (![A_6, C_12]: (~r2_orders_2(A_6, C_12, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.11/4.34  tff(c_9242, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_9236, c_8])).
% 11.11/4.34  tff(c_9252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_9242])).
% 11.11/4.34  tff(c_9254, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_9232])).
% 11.11/4.34  tff(c_8747, plain, (![A_835, B_836, C_837]: (m1_subset_1(k3_orders_2(A_835, B_836, C_837), k1_zfmisc_1(u1_struct_0(A_835))) | ~m1_subset_1(C_837, u1_struct_0(A_835)) | ~m1_subset_1(B_836, k1_zfmisc_1(u1_struct_0(A_835))) | ~l1_orders_2(A_835) | ~v5_orders_2(A_835) | ~v4_orders_2(A_835) | ~v3_orders_2(A_835) | v2_struct_0(A_835))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.11/4.34  tff(c_8818, plain, (![A_849, A_850, B_851, C_852]: (m1_subset_1(A_849, u1_struct_0(A_850)) | ~r2_hidden(A_849, k3_orders_2(A_850, B_851, C_852)) | ~m1_subset_1(C_852, u1_struct_0(A_850)) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0(A_850))) | ~l1_orders_2(A_850) | ~v5_orders_2(A_850) | ~v4_orders_2(A_850) | ~v3_orders_2(A_850) | v2_struct_0(A_850))), inference(resolution, [status(thm)], [c_8747, c_4])).
% 11.11/4.34  tff(c_8822, plain, (![A_850, B_851, C_852]: (m1_subset_1('#skF_1'(k3_orders_2(A_850, B_851, C_852)), u1_struct_0(A_850)) | ~m1_subset_1(C_852, u1_struct_0(A_850)) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0(A_850))) | ~l1_orders_2(A_850) | ~v5_orders_2(A_850) | ~v4_orders_2(A_850) | ~v3_orders_2(A_850) | v2_struct_0(A_850) | k3_orders_2(A_850, B_851, C_852)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_8818])).
% 11.11/4.34  tff(c_8930, plain, (![B_877, D_878, A_879, C_880]: (r2_hidden(B_877, D_878) | ~r2_hidden(B_877, k3_orders_2(A_879, D_878, C_880)) | ~m1_subset_1(D_878, k1_zfmisc_1(u1_struct_0(A_879))) | ~m1_subset_1(C_880, u1_struct_0(A_879)) | ~m1_subset_1(B_877, u1_struct_0(A_879)) | ~l1_orders_2(A_879) | ~v5_orders_2(A_879) | ~v4_orders_2(A_879) | ~v3_orders_2(A_879) | v2_struct_0(A_879))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.11/4.34  tff(c_9057, plain, (![A_911, D_912, C_913]: (r2_hidden('#skF_1'(k3_orders_2(A_911, D_912, C_913)), D_912) | ~m1_subset_1(D_912, k1_zfmisc_1(u1_struct_0(A_911))) | ~m1_subset_1(C_913, u1_struct_0(A_911)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_911, D_912, C_913)), u1_struct_0(A_911)) | ~l1_orders_2(A_911) | ~v5_orders_2(A_911) | ~v4_orders_2(A_911) | ~v3_orders_2(A_911) | v2_struct_0(A_911) | k3_orders_2(A_911, D_912, C_913)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_8930])).
% 11.11/4.34  tff(c_9069, plain, (![A_916, B_917, C_918]: (r2_hidden('#skF_1'(k3_orders_2(A_916, B_917, C_918)), B_917) | ~m1_subset_1(C_918, u1_struct_0(A_916)) | ~m1_subset_1(B_917, k1_zfmisc_1(u1_struct_0(A_916))) | ~l1_orders_2(A_916) | ~v5_orders_2(A_916) | ~v4_orders_2(A_916) | ~v3_orders_2(A_916) | v2_struct_0(A_916) | k3_orders_2(A_916, B_917, C_918)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8822, c_9057])).
% 11.11/4.34  tff(c_9062, plain, (![D_912, C_913]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), D_912) | ~m1_subset_1(D_912, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_913, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_912, C_913)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_9057])).
% 11.11/4.34  tff(c_9066, plain, (![D_912, C_913]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), D_912) | ~m1_subset_1(D_912, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_913, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_912, C_913)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_9062])).
% 11.11/4.34  tff(c_9067, plain, (![D_912, C_913]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), D_912) | ~m1_subset_1(D_912, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_913, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_912, C_913)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_912, C_913)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_9066])).
% 11.11/4.34  tff(c_9072, plain, (![C_918]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_918)), '#skF_5') | ~m1_subset_1(C_918, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_918)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9069, c_9067])).
% 11.11/4.34  tff(c_9086, plain, (![C_918]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_918)), '#skF_5') | ~m1_subset_1(C_918, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_918)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_8716, c_9072])).
% 11.11/4.34  tff(c_9087, plain, (![C_918]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_918)), '#skF_5') | ~m1_subset_1(C_918, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_918)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_9086])).
% 11.11/4.34  tff(c_32, plain, (![A_53, D_81, B_69, E_83]: (r3_orders_2(A_53, k1_funct_1(D_81, u1_struct_0(A_53)), B_69) | ~r2_hidden(B_69, E_83) | ~m2_orders_2(E_83, A_53, D_81) | ~m1_orders_1(D_81, k1_orders_1(u1_struct_0(A_53))) | ~m1_subset_1(k1_funct_1(D_81, u1_struct_0(A_53)), u1_struct_0(A_53)) | ~m1_subset_1(B_69, u1_struct_0(A_53)) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_186])).
% 11.11/4.34  tff(c_16423, plain, (![C_1519, D_1518, A_1516, B_1520, A_1517]: (r3_orders_2(A_1516, k1_funct_1(D_1518, u1_struct_0(A_1516)), '#skF_1'(k3_orders_2(A_1517, B_1520, C_1519))) | ~m2_orders_2(B_1520, A_1516, D_1518) | ~m1_orders_1(D_1518, k1_orders_1(u1_struct_0(A_1516))) | ~m1_subset_1(k1_funct_1(D_1518, u1_struct_0(A_1516)), u1_struct_0(A_1516)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1517, B_1520, C_1519)), u1_struct_0(A_1516)) | ~l1_orders_2(A_1516) | ~v5_orders_2(A_1516) | ~v4_orders_2(A_1516) | ~v3_orders_2(A_1516) | v2_struct_0(A_1516) | ~m1_subset_1(C_1519, u1_struct_0(A_1517)) | ~m1_subset_1(B_1520, k1_zfmisc_1(u1_struct_0(A_1517))) | ~l1_orders_2(A_1517) | ~v5_orders_2(A_1517) | ~v4_orders_2(A_1517) | ~v3_orders_2(A_1517) | v2_struct_0(A_1517) | k3_orders_2(A_1517, B_1520, C_1519)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9069, c_32])).
% 11.11/4.34  tff(c_16428, plain, (![A_1517, B_1520, C_1519]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1517, B_1520, C_1519))) | ~m2_orders_2(B_1520, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2(A_1517, B_1520, C_1519)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_1519, u1_struct_0(A_1517)) | ~m1_subset_1(B_1520, k1_zfmisc_1(u1_struct_0(A_1517))) | ~l1_orders_2(A_1517) | ~v5_orders_2(A_1517) | ~v4_orders_2(A_1517) | ~v3_orders_2(A_1517) | v2_struct_0(A_1517) | k3_orders_2(A_1517, B_1520, C_1519)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_16423])).
% 11.11/4.34  tff(c_16431, plain, (![A_1517, B_1520, C_1519]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1517, B_1520, C_1519))) | ~m2_orders_2(B_1520, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(k3_orders_2(A_1517, B_1520, C_1519)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_1519, u1_struct_0(A_1517)) | ~m1_subset_1(B_1520, k1_zfmisc_1(u1_struct_0(A_1517))) | ~l1_orders_2(A_1517) | ~v5_orders_2(A_1517) | ~v4_orders_2(A_1517) | ~v3_orders_2(A_1517) | v2_struct_0(A_1517) | k3_orders_2(A_1517, B_1520, C_1519)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_36, c_40, c_16428])).
% 11.11/4.34  tff(c_16988, plain, (![A_1551, B_1552, C_1553]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2(A_1551, B_1552, C_1553))) | ~m2_orders_2(B_1552, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(k3_orders_2(A_1551, B_1552, C_1553)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_1553, u1_struct_0(A_1551)) | ~m1_subset_1(B_1552, k1_zfmisc_1(u1_struct_0(A_1551))) | ~l1_orders_2(A_1551) | ~v5_orders_2(A_1551) | ~v4_orders_2(A_1551) | ~v3_orders_2(A_1551) | v2_struct_0(A_1551) | k3_orders_2(A_1551, B_1552, C_1553)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_16431])).
% 11.11/4.34  tff(c_16996, plain, (![B_851, C_852]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852))) | ~m2_orders_2(B_851, '#skF_2', '#skF_4') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8822, c_16988])).
% 11.11/4.34  tff(c_17006, plain, (![B_851, C_852]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852))) | ~m2_orders_2(B_851, '#skF_2', '#skF_4') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_16996])).
% 11.11/4.34  tff(c_17009, plain, (![B_1554, C_1555]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1554, C_1555))) | ~m2_orders_2(B_1554, '#skF_2', '#skF_4') | ~m1_subset_1(C_1555, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1554, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1554, C_1555)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_17006])).
% 11.11/4.34  tff(c_17011, plain, (![B_1554, C_1555]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1554, C_1555))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1554, C_1555)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_1554, '#skF_2', '#skF_4') | ~m1_subset_1(C_1555, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1554, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1554, C_1555)=k1_xboole_0)), inference(resolution, [status(thm)], [c_17009, c_20])).
% 11.11/4.34  tff(c_17014, plain, (![B_1554, C_1555]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1554, C_1555))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1554, C_1555)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_1554, '#skF_2', '#skF_4') | ~m1_subset_1(C_1555, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1554, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1554, C_1555)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_17011])).
% 11.11/4.34  tff(c_17016, plain, (![B_1556, C_1557]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1556, C_1557))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', B_1556, C_1557)), u1_struct_0('#skF_2')) | ~m2_orders_2(B_1556, '#skF_2', '#skF_4') | ~m1_subset_1(C_1557, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1556, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1556, C_1557)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_17014])).
% 11.11/4.34  tff(c_17024, plain, (![B_851, C_852]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852))) | ~m2_orders_2(B_851, '#skF_2', '#skF_4') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8822, c_17016])).
% 11.11/4.34  tff(c_17034, plain, (![B_851, C_852]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852))) | ~m2_orders_2(B_851, '#skF_2', '#skF_4') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_17024])).
% 11.11/4.34  tff(c_17037, plain, (![B_1558, C_1559]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_1558, C_1559))) | ~m2_orders_2(B_1558, '#skF_2', '#skF_4') | ~m1_subset_1(C_1559, u1_struct_0('#skF_2')) | ~m1_subset_1(B_1558, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1558, C_1559)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_17034])).
% 11.11/4.34  tff(c_8999, plain, (![A_892, B_893, C_894, D_895]: (r2_orders_2(A_892, B_893, C_894) | ~r2_hidden(B_893, k3_orders_2(A_892, D_895, C_894)) | ~m1_subset_1(D_895, k1_zfmisc_1(u1_struct_0(A_892))) | ~m1_subset_1(C_894, u1_struct_0(A_892)) | ~m1_subset_1(B_893, u1_struct_0(A_892)) | ~l1_orders_2(A_892) | ~v5_orders_2(A_892) | ~v4_orders_2(A_892) | ~v3_orders_2(A_892) | v2_struct_0(A_892))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.11/4.34  tff(c_9136, plain, (![A_926, D_927, C_928]: (r2_orders_2(A_926, '#skF_1'(k3_orders_2(A_926, D_927, C_928)), C_928) | ~m1_subset_1(D_927, k1_zfmisc_1(u1_struct_0(A_926))) | ~m1_subset_1(C_928, u1_struct_0(A_926)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_926, D_927, C_928)), u1_struct_0(A_926)) | ~l1_orders_2(A_926) | ~v5_orders_2(A_926) | ~v4_orders_2(A_926) | ~v3_orders_2(A_926) | v2_struct_0(A_926) | k3_orders_2(A_926, D_927, C_928)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_8999])).
% 11.11/4.34  tff(c_9141, plain, (![D_927, C_928]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_927, C_928)), C_928) | ~m1_subset_1(D_927, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_928, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_927, C_928)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_927, C_928)), '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_9136])).
% 11.11/4.34  tff(c_9145, plain, (![D_927, C_928]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_927, C_928)), C_928) | ~m1_subset_1(D_927, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_928, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_927, C_928)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_927, C_928)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_9141])).
% 11.11/4.34  tff(c_9147, plain, (![D_929, C_930]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_929, C_930)), C_930) | ~m1_subset_1(D_929, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_930, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_929, C_930)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_929, C_930)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_9145])).
% 11.11/4.34  tff(c_10, plain, (![A_6, B_10, C_12]: (r1_orders_2(A_6, B_10, C_12) | ~r2_orders_2(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.11/4.34  tff(c_9151, plain, (![D_929, C_930]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_929, C_930)), C_930) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_929, C_930)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~m1_subset_1(D_929, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_930, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_929, C_930)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_929, C_930)), '#skF_5'))), inference(resolution, [status(thm)], [c_9147, c_10])).
% 11.11/4.34  tff(c_9596, plain, (![D_984, C_985]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_984, C_985)), C_985) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_984, C_985)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_984, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_985, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_984, C_985)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_984, C_985)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9151])).
% 11.11/4.34  tff(c_9599, plain, (![B_851, C_852]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852)), C_852) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_851, C_852)), '#skF_5') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8822, c_9596])).
% 11.11/4.34  tff(c_9605, plain, (![B_851, C_852]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_851, C_852)), C_852) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_851, C_852)), '#skF_5') | ~m1_subset_1(C_852, u1_struct_0('#skF_2')) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', B_851, C_852)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_9599])).
% 11.11/4.34  tff(c_9608, plain, (![B_986, C_987]: (r1_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', B_986, C_987)), C_987) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_986, C_987)), '#skF_5') | ~m1_subset_1(C_987, u1_struct_0('#skF_2')) | ~m1_subset_1(B_986, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_986, C_987)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_9605])).
% 11.11/4.34  tff(c_6, plain, (![A_6, B_10, C_12]: (r2_orders_2(A_6, B_10, C_12) | C_12=B_10 | ~r1_orders_2(A_6, B_10, C_12) | ~m1_subset_1(C_12, u1_struct_0(A_6)) | ~m1_subset_1(B_10, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.11/4.34  tff(c_8730, plain, (![B_10, A_833]: (r2_orders_2('#skF_2', B_10, A_833) | B_10=A_833 | ~r1_orders_2('#skF_2', B_10, A_833) | ~m1_subset_1(B_10, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r2_hidden(A_833, '#skF_5'))), inference(resolution, [status(thm)], [c_8720, c_6])).
% 11.11/4.34  tff(c_8785, plain, (![B_844, A_845]: (r2_orders_2('#skF_2', B_844, A_845) | B_844=A_845 | ~r1_orders_2('#skF_2', B_844, A_845) | ~m1_subset_1(B_844, u1_struct_0('#skF_2')) | ~r2_hidden(A_845, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8730])).
% 11.11/4.34  tff(c_8791, plain, (![A_845]: (r2_orders_2('#skF_2', '#skF_3', A_845) | A_845='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_845) | ~r2_hidden(A_845, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_8785])).
% 11.11/4.34  tff(c_8833, plain, (![B_860, A_845]: (~r1_orders_2('#skF_2', B_860, '#skF_3') | r2_orders_2('#skF_2', B_860, A_845) | ~m1_subset_1(A_845, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_860, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | A_845='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_845) | ~r2_hidden(A_845, '#skF_5'))), inference(resolution, [status(thm)], [c_8791, c_8829])).
% 11.11/4.34  tff(c_8852, plain, (![B_863, A_864]: (~r1_orders_2('#skF_2', B_863, '#skF_3') | r2_orders_2('#skF_2', B_863, A_864) | ~m1_subset_1(A_864, u1_struct_0('#skF_2')) | ~m1_subset_1(B_863, u1_struct_0('#skF_2')) | A_864='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_864) | ~r2_hidden(A_864, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_8833])).
% 11.11/4.34  tff(c_8862, plain, (![B_865, A_866]: (~r1_orders_2('#skF_2', B_865, '#skF_3') | r2_orders_2('#skF_2', B_865, A_866) | ~m1_subset_1(B_865, u1_struct_0('#skF_2')) | A_866='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_866) | ~r2_hidden(A_866, '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_8852])).
% 11.11/4.34  tff(c_8871, plain, (![A_867, A_868]: (~r1_orders_2('#skF_2', A_867, '#skF_3') | r2_orders_2('#skF_2', A_867, A_868) | A_868='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_868) | ~r2_hidden(A_868, '#skF_5') | ~r2_hidden(A_867, '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_8862])).
% 11.11/4.34  tff(c_8878, plain, (![A_868]: (~m1_subset_1(A_868, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~r1_orders_2('#skF_2', A_868, '#skF_3') | A_868='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_868) | ~r2_hidden(A_868, '#skF_5'))), inference(resolution, [status(thm)], [c_8871, c_8])).
% 11.11/4.34  tff(c_8888, plain, (![A_869]: (~m1_subset_1(A_869, u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', A_869, '#skF_3') | A_869='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_869) | ~r2_hidden(A_869, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8878])).
% 11.11/4.34  tff(c_8895, plain, (![A_3]: (~r1_orders_2('#skF_2', A_3, '#skF_3') | A_3='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', A_3) | ~r2_hidden(A_3, '#skF_5'))), inference(resolution, [status(thm)], [c_8719, c_8888])).
% 11.11/4.34  tff(c_9627, plain, (![B_986]: ('#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_986, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_986, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_9608, c_8895])).
% 11.11/4.34  tff(c_9644, plain, (![B_986]: ('#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_986, '#skF_3')), '#skF_5') | ~m1_subset_1(B_986, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_986, '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_9627])).
% 11.11/4.34  tff(c_17066, plain, (![B_1558]: ('#skF_1'(k3_orders_2('#skF_2', B_1558, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1558, '#skF_3')), '#skF_5') | ~m2_orders_2(B_1558, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_1558, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1558, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_17037, c_9644])).
% 11.11/4.34  tff(c_17132, plain, (![B_1560]: ('#skF_1'(k3_orders_2('#skF_2', B_1560, '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_1560, '#skF_3')), '#skF_5') | ~m2_orders_2(B_1560, '#skF_2', '#skF_4') | ~m1_subset_1(B_1560, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', B_1560, '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_17066])).
% 11.11/4.34  tff(c_17136, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9087, c_17132])).
% 11.11/4.34  tff(c_17143, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8716, c_38, c_17136])).
% 11.11/4.34  tff(c_17144, plain, ('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_34, c_17143])).
% 11.11/4.34  tff(c_9142, plain, (![A_850, B_851, C_852]: (r2_orders_2(A_850, '#skF_1'(k3_orders_2(A_850, B_851, C_852)), C_852) | ~m1_subset_1(C_852, u1_struct_0(A_850)) | ~m1_subset_1(B_851, k1_zfmisc_1(u1_struct_0(A_850))) | ~l1_orders_2(A_850) | ~v5_orders_2(A_850) | ~v4_orders_2(A_850) | ~v3_orders_2(A_850) | v2_struct_0(A_850) | k3_orders_2(A_850, B_851, C_852)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8822, c_9136])).
% 11.11/4.34  tff(c_17317, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_17144, c_9142])).
% 11.11/4.34  tff(c_17522, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_8716, c_42, c_17317])).
% 11.11/4.34  tff(c_17524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_52, c_9254, c_17522])).
% 11.11/4.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.11/4.34  
% 11.11/4.34  Inference rules
% 11.11/4.34  ----------------------
% 11.11/4.34  #Ref     : 0
% 11.11/4.34  #Sup     : 3262
% 11.11/4.34  #Fact    : 0
% 11.11/4.34  #Define  : 0
% 11.11/4.34  #Split   : 30
% 11.11/4.34  #Chain   : 0
% 11.11/4.34  #Close   : 0
% 11.11/4.34  
% 11.11/4.34  Ordering : KBO
% 11.11/4.34  
% 11.11/4.34  Simplification rules
% 11.11/4.34  ----------------------
% 11.11/4.34  #Subsume      : 1506
% 11.11/4.34  #Demod        : 5777
% 11.11/4.34  #Tautology    : 275
% 11.11/4.34  #SimpNegUnit  : 931
% 11.11/4.34  #BackRed      : 172
% 11.11/4.34  
% 11.11/4.34  #Partial instantiations: 0
% 11.11/4.34  #Strategies tried      : 1
% 11.11/4.34  
% 11.11/4.34  Timing (in seconds)
% 11.11/4.34  ----------------------
% 11.11/4.35  Preprocessing        : 0.34
% 11.11/4.35  Parsing              : 0.18
% 11.11/4.35  CNF conversion       : 0.03
% 11.11/4.35  Main loop            : 3.22
% 11.11/4.35  Inferencing          : 0.98
% 11.11/4.35  Reduction            : 1.02
% 11.11/4.35  Demodulation         : 0.68
% 11.11/4.35  BG Simplification    : 0.08
% 11.11/4.35  Subsumption          : 0.98
% 11.11/4.35  Abstraction          : 0.17
% 11.11/4.35  MUC search           : 0.00
% 11.11/4.35  Cooper               : 0.00
% 11.11/4.35  Total                : 3.61
% 11.11/4.35  Index Insertion      : 0.00
% 11.11/4.35  Index Deletion       : 0.00
% 11.11/4.35  Index Matching       : 0.00
% 11.11/4.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
