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
% DateTime   : Thu Dec  3 10:26:28 EST 2020

% Result     : Theorem 19.38s
% Output     : CNFRefutation 19.67s
% Verified   : 
% Statistics : Number of formulae       :  241 (1878 expanded)
%              Number of leaves         :   41 ( 706 expanded)
%              Depth                    :   27
%              Number of atoms          : 1089 (11634 expanded)
%              Number of equality atoms :   50 (1082 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_184,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( ~ r1_tsep_1(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(k2_tsep_1(A,B,C)))
                     => ( ? [E] :
                            ( m1_subset_1(E,u1_struct_0(B))
                            & E = D )
                        & ? [E] :
                            ( m1_subset_1(E,u1_struct_0(C))
                            & E = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_148,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_58,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_52,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_40,plain,(
    ! [A_67,B_68,C_69] :
      ( v1_pre_topc(k2_tsep_1(A_67,B_68,C_69))
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_23916,plain,(
    ! [C_1502,A_1503,B_1504] :
      ( m1_subset_1(C_1502,u1_struct_0(A_1503))
      | ~ m1_subset_1(C_1502,u1_struct_0(B_1504))
      | ~ m1_pre_topc(B_1504,A_1503)
      | v2_struct_0(B_1504)
      | ~ l1_pre_topc(A_1503)
      | v2_struct_0(A_1503) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_23924,plain,(
    ! [A_1503] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_1503))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_1503)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_1503)
      | v2_struct_0(A_1503) ) ),
    inference(resolution,[status(thm)],[c_50,c_23916])).

tff(c_23965,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_23924])).

tff(c_24428,plain,(
    ! [A_1575,B_1576,C_1577] :
      ( ~ v2_struct_0(k2_tsep_1(A_1575,B_1576,C_1577))
      | ~ m1_pre_topc(C_1577,A_1575)
      | v2_struct_0(C_1577)
      | ~ m1_pre_topc(B_1576,A_1575)
      | v2_struct_0(B_1576)
      | ~ l1_pre_topc(A_1575)
      | v2_struct_0(A_1575) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24431,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_23965,c_24428])).

tff(c_24434,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_24431])).

tff(c_24436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_24434])).

tff(c_24438,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_23924])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_25074,plain,(
    ! [A_1683,B_1684,C_1685] :
      ( m1_pre_topc(k2_tsep_1(A_1683,B_1684,C_1685),A_1683)
      | ~ m1_pre_topc(C_1685,A_1683)
      | v2_struct_0(C_1685)
      | ~ m1_pre_topc(B_1684,A_1683)
      | v2_struct_0(B_1684)
      | ~ l1_pre_topc(A_1683)
      | v2_struct_0(A_1683) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_30] : k2_subset_1(A_30) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_31] : m1_subset_1(k2_subset_1(A_31),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [A_31] : m1_subset_1(A_31,k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_88,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(A_126,B_127)
      | ~ m1_subset_1(A_126,k1_zfmisc_1(B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_31] : r1_tarski(A_31,A_31) ),
    inference(resolution,[status(thm)],[c_67,c_88])).

tff(c_24794,plain,(
    ! [B_1627,C_1628,A_1629] :
      ( m1_pre_topc(B_1627,C_1628)
      | ~ r1_tarski(u1_struct_0(B_1627),u1_struct_0(C_1628))
      | ~ m1_pre_topc(C_1628,A_1629)
      | ~ m1_pre_topc(B_1627,A_1629)
      | ~ l1_pre_topc(A_1629)
      | ~ v2_pre_topc(A_1629) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24804,plain,(
    ! [B_1627,A_1629] :
      ( m1_pre_topc(B_1627,B_1627)
      | ~ m1_pre_topc(B_1627,A_1629)
      | ~ l1_pre_topc(A_1629)
      | ~ v2_pre_topc(A_1629) ) ),
    inference(resolution,[status(thm)],[c_92,c_24794])).

tff(c_25090,plain,(
    ! [A_1683,B_1684,C_1685] :
      ( m1_pre_topc(k2_tsep_1(A_1683,B_1684,C_1685),k2_tsep_1(A_1683,B_1684,C_1685))
      | ~ v2_pre_topc(A_1683)
      | ~ m1_pre_topc(C_1685,A_1683)
      | v2_struct_0(C_1685)
      | ~ m1_pre_topc(B_1684,A_1683)
      | v2_struct_0(B_1684)
      | ~ l1_pre_topc(A_1683)
      | v2_struct_0(A_1683) ) ),
    inference(resolution,[status(thm)],[c_25074,c_24804])).

tff(c_38,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_pre_topc(k2_tsep_1(A_67,B_68,C_69),A_67)
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_25300,plain,(
    ! [A_1734,B_1735,C_1736] :
      ( u1_struct_0(k2_tsep_1(A_1734,B_1735,C_1736)) = k3_xboole_0(u1_struct_0(B_1735),u1_struct_0(C_1736))
      | ~ m1_pre_topc(k2_tsep_1(A_1734,B_1735,C_1736),A_1734)
      | ~ v1_pre_topc(k2_tsep_1(A_1734,B_1735,C_1736))
      | v2_struct_0(k2_tsep_1(A_1734,B_1735,C_1736))
      | r1_tsep_1(B_1735,C_1736)
      | ~ m1_pre_topc(C_1736,A_1734)
      | v2_struct_0(C_1736)
      | ~ m1_pre_topc(B_1735,A_1734)
      | v2_struct_0(B_1735)
      | ~ l1_pre_topc(A_1734)
      | v2_struct_0(A_1734) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26511,plain,(
    ! [A_1799,B_1800,C_1801] :
      ( u1_struct_0(k2_tsep_1(A_1799,B_1800,C_1801)) = k3_xboole_0(u1_struct_0(B_1800),u1_struct_0(C_1801))
      | ~ v1_pre_topc(k2_tsep_1(A_1799,B_1800,C_1801))
      | v2_struct_0(k2_tsep_1(A_1799,B_1800,C_1801))
      | r1_tsep_1(B_1800,C_1801)
      | ~ m1_pre_topc(C_1801,A_1799)
      | v2_struct_0(C_1801)
      | ~ m1_pre_topc(B_1800,A_1799)
      | v2_struct_0(B_1800)
      | ~ l1_pre_topc(A_1799)
      | v2_struct_0(A_1799) ) ),
    inference(resolution,[status(thm)],[c_38,c_25300])).

tff(c_24437,plain,(
    ! [A_1503] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_1503))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_1503)
      | ~ l1_pre_topc(A_1503)
      | v2_struct_0(A_1503) ) ),
    inference(splitRight,[status(thm)],[c_23924])).

tff(c_30046,plain,(
    ! [B_1975,C_1976,A_1977] :
      ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0(B_1975),u1_struct_0(C_1976)))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1(A_1977,B_1975,C_1976))
      | ~ l1_pre_topc(k2_tsep_1(A_1977,B_1975,C_1976))
      | v2_struct_0(k2_tsep_1(A_1977,B_1975,C_1976))
      | ~ v1_pre_topc(k2_tsep_1(A_1977,B_1975,C_1976))
      | v2_struct_0(k2_tsep_1(A_1977,B_1975,C_1976))
      | r1_tsep_1(B_1975,C_1976)
      | ~ m1_pre_topc(C_1976,A_1977)
      | v2_struct_0(C_1976)
      | ~ m1_pre_topc(B_1975,A_1977)
      | v2_struct_0(B_1975)
      | ~ l1_pre_topc(A_1977)
      | v2_struct_0(A_1977) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26511,c_24437])).

tff(c_30049,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_25090,c_30046])).

tff(c_30052,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_30049])).

tff(c_30053,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_24438,c_30052])).

tff(c_30054,plain,(
    ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30053])).

tff(c_30057,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_30054])).

tff(c_30060,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_30057])).

tff(c_30062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_30060])).

tff(c_30064,plain,(
    v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30053])).

tff(c_25303,plain,(
    ! [A_67,B_68,C_69] :
      ( u1_struct_0(k2_tsep_1(A_67,B_68,C_69)) = k3_xboole_0(u1_struct_0(B_68),u1_struct_0(C_69))
      | ~ v1_pre_topc(k2_tsep_1(A_67,B_68,C_69))
      | v2_struct_0(k2_tsep_1(A_67,B_68,C_69))
      | r1_tsep_1(B_68,C_69)
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_38,c_25300])).

tff(c_33004,plain,(
    ! [A_2173,B_2171,C_2172,A_2170] :
      ( u1_struct_0(k2_tsep_1(A_2173,B_2171,C_2172)) = u1_struct_0(k2_tsep_1(A_2170,B_2171,C_2172))
      | ~ v1_pre_topc(k2_tsep_1(A_2173,B_2171,C_2172))
      | v2_struct_0(k2_tsep_1(A_2173,B_2171,C_2172))
      | r1_tsep_1(B_2171,C_2172)
      | ~ m1_pre_topc(C_2172,A_2173)
      | v2_struct_0(C_2172)
      | ~ m1_pre_topc(B_2171,A_2173)
      | v2_struct_0(B_2171)
      | ~ l1_pre_topc(A_2173)
      | v2_struct_0(A_2173)
      | ~ v1_pre_topc(k2_tsep_1(A_2170,B_2171,C_2172))
      | v2_struct_0(k2_tsep_1(A_2170,B_2171,C_2172))
      | r1_tsep_1(B_2171,C_2172)
      | ~ m1_pre_topc(C_2172,A_2170)
      | v2_struct_0(C_2172)
      | ~ m1_pre_topc(B_2171,A_2170)
      | v2_struct_0(B_2171)
      | ~ l1_pre_topc(A_2170)
      | v2_struct_0(A_2170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25303,c_26511])).

tff(c_33508,plain,(
    ! [A_2170] :
      ( u1_struct_0(k2_tsep_1(A_2170,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_2170,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_2170,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_2170)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_2170)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_2170)
      | v2_struct_0(A_2170) ) ),
    inference(resolution,[status(thm)],[c_33004,c_24438])).

tff(c_33552,plain,(
    ! [A_2170] :
      ( u1_struct_0(k2_tsep_1(A_2170,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_2170,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_2170,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_2170)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_2170)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_2170)
      | v2_struct_0(A_2170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_30064,c_33508])).

tff(c_33635,plain,(
    ! [A_2179] :
      ( u1_struct_0(k2_tsep_1(A_2179,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_2179,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_2179,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2179)
      | ~ m1_pre_topc('#skF_2',A_2179)
      | ~ l1_pre_topc(A_2179)
      | v2_struct_0(A_2179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_66,c_33552])).

tff(c_42,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ v2_struct_0(k2_tsep_1(A_67,B_68,C_69))
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_33638,plain,(
    ! [A_2179] :
      ( v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | u1_struct_0(k2_tsep_1(A_2179,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_2179,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2179)
      | ~ m1_pre_topc('#skF_2',A_2179)
      | ~ l1_pre_topc(A_2179)
      | v2_struct_0(A_2179) ) ),
    inference(resolution,[status(thm)],[c_33635,c_42])).

tff(c_33650,plain,(
    ! [A_2180] :
      ( u1_struct_0(k2_tsep_1(A_2180,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_2180,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2180)
      | ~ m1_pre_topc('#skF_2',A_2180)
      | ~ l1_pre_topc(A_2180)
      | v2_struct_0(A_2180) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_33638])).

tff(c_33657,plain,(
    ! [A_67] :
      ( u1_struct_0(k2_tsep_1(A_67,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_67)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_67)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_40,c_33650])).

tff(c_33666,plain,(
    ! [A_2181] :
      ( u1_struct_0(k2_tsep_1(A_2181,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_33657])).

tff(c_27689,plain,(
    ! [A_1832,B_1833,C_1834] :
      ( u1_struct_0(k2_tsep_1(A_1832,B_1833,C_1834)) = k3_xboole_0(u1_struct_0(B_1833),u1_struct_0(C_1834))
      | ~ v1_pre_topc(k2_tsep_1(A_1832,B_1833,C_1834))
      | r1_tsep_1(B_1833,C_1834)
      | ~ m1_pre_topc(C_1834,A_1832)
      | v2_struct_0(C_1834)
      | ~ m1_pre_topc(B_1833,A_1832)
      | v2_struct_0(B_1833)
      | ~ l1_pre_topc(A_1832)
      | v2_struct_0(A_1832) ) ),
    inference(resolution,[status(thm)],[c_26511,c_42])).

tff(c_27693,plain,(
    ! [A_1835,B_1836,C_1837] :
      ( u1_struct_0(k2_tsep_1(A_1835,B_1836,C_1837)) = k3_xboole_0(u1_struct_0(B_1836),u1_struct_0(C_1837))
      | r1_tsep_1(B_1836,C_1837)
      | ~ m1_pre_topc(C_1837,A_1835)
      | v2_struct_0(C_1837)
      | ~ m1_pre_topc(B_1836,A_1835)
      | v2_struct_0(B_1836)
      | ~ l1_pre_topc(A_1835)
      | v2_struct_0(A_1835) ) ),
    inference(resolution,[status(thm)],[c_40,c_27689])).

tff(c_23761,plain,(
    ! [A_1451,B_1452,C_1453] :
      ( k9_subset_1(A_1451,B_1452,C_1453) = k3_xboole_0(B_1452,C_1453)
      | ~ m1_subset_1(C_1453,k1_zfmisc_1(A_1451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_23767,plain,(
    ! [A_31,B_1452] : k9_subset_1(A_31,B_1452,A_31) = k3_xboole_0(B_1452,A_31) ),
    inference(resolution,[status(thm)],[c_67,c_23761])).

tff(c_23794,plain,(
    ! [A_1463,B_1464,C_1465] :
      ( m1_subset_1(k9_subset_1(A_1463,B_1464,C_1465),k1_zfmisc_1(A_1463))
      | ~ m1_subset_1(C_1465,k1_zfmisc_1(A_1463)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23802,plain,(
    ! [B_1452,A_31] :
      ( m1_subset_1(k3_xboole_0(B_1452,A_31),k1_zfmisc_1(A_31))
      | ~ m1_subset_1(A_31,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23767,c_23794])).

tff(c_23807,plain,(
    ! [B_1466,A_1467] : m1_subset_1(k3_xboole_0(B_1466,A_1467),k1_zfmisc_1(A_1467)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_23802])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23814,plain,(
    ! [B_1466,A_1467] : r1_tarski(k3_xboole_0(B_1466,A_1467),A_1467) ),
    inference(resolution,[status(thm)],[c_23807,c_26])).

tff(c_27867,plain,(
    ! [A_1835,B_1836,C_1837] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1835,B_1836,C_1837)),u1_struct_0(C_1837))
      | r1_tsep_1(B_1836,C_1837)
      | ~ m1_pre_topc(C_1837,A_1835)
      | v2_struct_0(C_1837)
      | ~ m1_pre_topc(B_1836,A_1835)
      | v2_struct_0(B_1836)
      | ~ l1_pre_topc(A_1835)
      | v2_struct_0(A_1835) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27693,c_23814])).

tff(c_33961,plain,(
    ! [A_2181] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_2181,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33666,c_27867])).

tff(c_34210,plain,(
    ! [A_2181] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_2181,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_33961])).

tff(c_34211,plain,(
    ! [A_2181] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_2181,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_34210])).

tff(c_94,plain,(
    ! [B_129,A_130] :
      ( l1_pre_topc(B_129)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_106,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_100])).

tff(c_24452,plain,(
    ! [A_1586] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_1586))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_1586)
      | ~ l1_pre_topc(A_1586)
      | v2_struct_0(A_1586) ) ),
    inference(splitRight,[status(thm)],[c_23924])).

tff(c_329,plain,(
    ! [C_201,A_202,B_203] :
      ( m1_subset_1(C_201,u1_struct_0(A_202))
      | ~ m1_subset_1(C_201,u1_struct_0(B_203))
      | ~ m1_pre_topc(B_203,A_202)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_332,plain,(
    ! [A_202] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_202))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_202)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(resolution,[status(thm)],[c_50,c_329])).

tff(c_447,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_648,plain,(
    ! [A_259,B_260,C_261] :
      ( ~ v2_struct_0(k2_tsep_1(A_259,B_260,C_261))
      | ~ m1_pre_topc(C_261,A_259)
      | v2_struct_0(C_261)
      | ~ m1_pre_topc(B_260,A_259)
      | v2_struct_0(B_260)
      | ~ l1_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_651,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_447,c_648])).

tff(c_654,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_651])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_654])).

tff(c_658,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_1015,plain,(
    ! [A_326,B_327,C_328] :
      ( m1_pre_topc(k2_tsep_1(A_326,B_327,C_328),A_326)
      | ~ m1_pre_topc(C_328,A_326)
      | v2_struct_0(C_328)
      | ~ m1_pre_topc(B_327,A_326)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_670,plain,(
    ! [B_263,C_264,A_265] :
      ( m1_pre_topc(B_263,C_264)
      | ~ r1_tarski(u1_struct_0(B_263),u1_struct_0(C_264))
      | ~ m1_pre_topc(C_264,A_265)
      | ~ m1_pre_topc(B_263,A_265)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_674,plain,(
    ! [B_263,A_265] :
      ( m1_pre_topc(B_263,B_263)
      | ~ m1_pre_topc(B_263,A_265)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_92,c_670])).

tff(c_1027,plain,(
    ! [A_326,B_327,C_328] :
      ( m1_pre_topc(k2_tsep_1(A_326,B_327,C_328),k2_tsep_1(A_326,B_327,C_328))
      | ~ v2_pre_topc(A_326)
      | ~ m1_pre_topc(C_328,A_326)
      | v2_struct_0(C_328)
      | ~ m1_pre_topc(B_327,A_326)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(resolution,[status(thm)],[c_1015,c_674])).

tff(c_1370,plain,(
    ! [A_379,B_380,C_381] :
      ( u1_struct_0(k2_tsep_1(A_379,B_380,C_381)) = k3_xboole_0(u1_struct_0(B_380),u1_struct_0(C_381))
      | ~ m1_pre_topc(k2_tsep_1(A_379,B_380,C_381),A_379)
      | ~ v1_pre_topc(k2_tsep_1(A_379,B_380,C_381))
      | v2_struct_0(k2_tsep_1(A_379,B_380,C_381))
      | r1_tsep_1(B_380,C_381)
      | ~ m1_pre_topc(C_381,A_379)
      | v2_struct_0(C_381)
      | ~ m1_pre_topc(B_380,A_379)
      | v2_struct_0(B_380)
      | ~ l1_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2454,plain,(
    ! [A_439,B_440,C_441] :
      ( u1_struct_0(k2_tsep_1(A_439,B_440,C_441)) = k3_xboole_0(u1_struct_0(B_440),u1_struct_0(C_441))
      | ~ v1_pre_topc(k2_tsep_1(A_439,B_440,C_441))
      | v2_struct_0(k2_tsep_1(A_439,B_440,C_441))
      | r1_tsep_1(B_440,C_441)
      | ~ m1_pre_topc(C_441,A_439)
      | v2_struct_0(C_441)
      | ~ m1_pre_topc(B_440,A_439)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(resolution,[status(thm)],[c_38,c_1370])).

tff(c_657,plain,(
    ! [A_202] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_202))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_202)
      | ~ l1_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_5437,plain,(
    ! [B_587,C_588,A_589] :
      ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0(B_587),u1_struct_0(C_588)))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1(A_589,B_587,C_588))
      | ~ l1_pre_topc(k2_tsep_1(A_589,B_587,C_588))
      | v2_struct_0(k2_tsep_1(A_589,B_587,C_588))
      | ~ v1_pre_topc(k2_tsep_1(A_589,B_587,C_588))
      | v2_struct_0(k2_tsep_1(A_589,B_587,C_588))
      | r1_tsep_1(B_587,C_588)
      | ~ m1_pre_topc(C_588,A_589)
      | v2_struct_0(C_588)
      | ~ m1_pre_topc(B_587,A_589)
      | v2_struct_0(B_587)
      | ~ l1_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_657])).

tff(c_5440,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1027,c_5437])).

tff(c_5443,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_5440])).

tff(c_5444,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_658,c_5443])).

tff(c_5445,plain,(
    ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5444])).

tff(c_5448,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_5445])).

tff(c_5451,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_5448])).

tff(c_5453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_5451])).

tff(c_5455,plain,(
    v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5444])).

tff(c_1373,plain,(
    ! [A_67,B_68,C_69] :
      ( u1_struct_0(k2_tsep_1(A_67,B_68,C_69)) = k3_xboole_0(u1_struct_0(B_68),u1_struct_0(C_69))
      | ~ v1_pre_topc(k2_tsep_1(A_67,B_68,C_69))
      | v2_struct_0(k2_tsep_1(A_67,B_68,C_69))
      | r1_tsep_1(B_68,C_69)
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_38,c_1370])).

tff(c_8809,plain,(
    ! [A_779,B_777,C_778,A_776] :
      ( u1_struct_0(k2_tsep_1(A_779,B_777,C_778)) = u1_struct_0(k2_tsep_1(A_776,B_777,C_778))
      | ~ v1_pre_topc(k2_tsep_1(A_779,B_777,C_778))
      | v2_struct_0(k2_tsep_1(A_779,B_777,C_778))
      | r1_tsep_1(B_777,C_778)
      | ~ m1_pre_topc(C_778,A_779)
      | v2_struct_0(C_778)
      | ~ m1_pre_topc(B_777,A_779)
      | v2_struct_0(B_777)
      | ~ l1_pre_topc(A_779)
      | v2_struct_0(A_779)
      | ~ v1_pre_topc(k2_tsep_1(A_776,B_777,C_778))
      | v2_struct_0(k2_tsep_1(A_776,B_777,C_778))
      | r1_tsep_1(B_777,C_778)
      | ~ m1_pre_topc(C_778,A_776)
      | v2_struct_0(C_778)
      | ~ m1_pre_topc(B_777,A_776)
      | v2_struct_0(B_777)
      | ~ l1_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_2454])).

tff(c_9299,plain,(
    ! [A_776] :
      ( u1_struct_0(k2_tsep_1(A_776,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_776,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_776,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_776)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_776)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(resolution,[status(thm)],[c_8809,c_658])).

tff(c_9343,plain,(
    ! [A_776] :
      ( u1_struct_0(k2_tsep_1(A_776,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_776,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_776,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_776)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_776)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_5455,c_9299])).

tff(c_9572,plain,(
    ! [A_785] :
      ( u1_struct_0(k2_tsep_1(A_785,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_785,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_785,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_785)
      | ~ m1_pre_topc('#skF_2',A_785)
      | ~ l1_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_66,c_9343])).

tff(c_9575,plain,(
    ! [A_785] :
      ( v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | u1_struct_0(k2_tsep_1(A_785,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_785,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_785)
      | ~ m1_pre_topc('#skF_2',A_785)
      | ~ l1_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(resolution,[status(thm)],[c_9572,c_42])).

tff(c_9587,plain,(
    ! [A_786] :
      ( u1_struct_0(k2_tsep_1(A_786,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_786,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_786)
      | ~ m1_pre_topc('#skF_2',A_786)
      | ~ l1_pre_topc(A_786)
      | v2_struct_0(A_786) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_9575])).

tff(c_9594,plain,(
    ! [A_67] :
      ( u1_struct_0(k2_tsep_1(A_67,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_67)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_67)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_40,c_9587])).

tff(c_9603,plain,(
    ! [A_787] :
      ( u1_struct_0(k2_tsep_1(A_787,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_9594])).

tff(c_3476,plain,(
    ! [A_471,B_472,C_473] :
      ( u1_struct_0(k2_tsep_1(A_471,B_472,C_473)) = k3_xboole_0(u1_struct_0(B_472),u1_struct_0(C_473))
      | ~ v1_pre_topc(k2_tsep_1(A_471,B_472,C_473))
      | r1_tsep_1(B_472,C_473)
      | ~ m1_pre_topc(C_473,A_471)
      | v2_struct_0(C_473)
      | ~ m1_pre_topc(B_472,A_471)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_2454,c_42])).

tff(c_3649,plain,(
    ! [A_478,B_479,C_480] :
      ( u1_struct_0(k2_tsep_1(A_478,B_479,C_480)) = k3_xboole_0(u1_struct_0(B_479),u1_struct_0(C_480))
      | r1_tsep_1(B_479,C_480)
      | ~ m1_pre_topc(C_480,A_478)
      | v2_struct_0(C_480)
      | ~ m1_pre_topc(B_479,A_478)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(resolution,[status(thm)],[c_40,c_3476])).

tff(c_131,plain,(
    ! [A_138,B_139,C_140] :
      ( k9_subset_1(A_138,B_139,C_140) = k3_xboole_0(B_139,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_137,plain,(
    ! [A_31,B_139] : k9_subset_1(A_31,B_139,A_31) = k3_xboole_0(B_139,A_31) ),
    inference(resolution,[status(thm)],[c_67,c_131])).

tff(c_147,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1(k9_subset_1(A_143,B_144,C_145),k1_zfmisc_1(A_143))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [B_139,A_31] :
      ( m1_subset_1(k3_xboole_0(B_139,A_31),k1_zfmisc_1(A_31))
      | ~ m1_subset_1(A_31,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_147])).

tff(c_160,plain,(
    ! [B_146,A_147] : m1_subset_1(k3_xboole_0(B_146,A_147),k1_zfmisc_1(A_147)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_155])).

tff(c_167,plain,(
    ! [B_146,A_147] : r1_tarski(k3_xboole_0(B_146,A_147),A_147) ),
    inference(resolution,[status(thm)],[c_160,c_26])).

tff(c_3825,plain,(
    ! [A_478,B_479,C_480] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_478,B_479,C_480)),u1_struct_0(C_480))
      | r1_tsep_1(B_479,C_480)
      | ~ m1_pre_topc(C_480,A_478)
      | v2_struct_0(C_480)
      | ~ m1_pre_topc(B_479,A_478)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_167])).

tff(c_9862,plain,(
    ! [A_787] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_787,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9603,c_3825])).

tff(c_10127,plain,(
    ! [A_787] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_787,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_9862])).

tff(c_10128,plain,(
    ! [A_787] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_787,'#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_10127])).

tff(c_659,plain,(
    ! [A_262] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_262))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_262)
      | ~ l1_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_32,plain,(
    ! [C_51,A_45,B_49] :
      ( m1_subset_1(C_51,u1_struct_0(A_45))
      | ~ m1_subset_1(C_51,u1_struct_0(B_49))
      | ~ m1_pre_topc(B_49,A_45)
      | v2_struct_0(B_49)
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_708,plain,(
    ! [A_268,A_269] :
      ( m1_subset_1('#skF_4',u1_struct_0(A_268))
      | ~ m1_pre_topc(A_269,A_268)
      | ~ l1_pre_topc(A_268)
      | v2_struct_0(A_268)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_269)
      | ~ l1_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_659,c_32])).

tff(c_716,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_708])).

tff(c_731,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_62,c_716])).

tff(c_732,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_66,c_731])).

tff(c_733,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_9868,plain,(
    ! [A_787] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_787)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_787)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787)
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9603,c_3825])).

tff(c_10130,plain,(
    ! [A_787] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787)
      | ~ m1_pre_topc('#skF_3',A_787)
      | ~ m1_pre_topc('#skF_2',A_787)
      | ~ l1_pre_topc(A_787)
      | v2_struct_0(A_787) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_9868])).

tff(c_11635,plain,(
    r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10130])).

tff(c_46,plain,(
    ! [B_74,C_76,A_70] :
      ( m1_pre_topc(B_74,C_76)
      | ~ r1_tarski(u1_struct_0(B_74),u1_struct_0(C_76))
      | ~ m1_pre_topc(C_76,A_70)
      | ~ m1_pre_topc(B_74,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_11637,plain,(
    ! [A_70] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_70)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_11635,c_46])).

tff(c_11647,plain,(
    ! [A_827] :
      ( ~ m1_pre_topc('#skF_3',A_827)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_827)
      | ~ l1_pre_topc(A_827)
      | ~ v2_pre_topc(A_827) ) ),
    inference(negUnitSimplification,[status(thm)],[c_733,c_11637])).

tff(c_11655,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_11647])).

tff(c_11662,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_11655])).

tff(c_11664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_11662])).

tff(c_11666,plain,(
    ~ r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10130])).

tff(c_11669,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10128,c_11666])).

tff(c_11681,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_11669])).

tff(c_11683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_11681])).

tff(c_11685,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_30,plain,(
    ! [B_44,A_42] :
      ( l1_pre_topc(B_44)
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11697,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_11685,c_30])).

tff(c_11707,plain,(
    l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_11697])).

tff(c_12029,plain,(
    ! [A_879,B_880,C_881] :
      ( m1_pre_topc(k2_tsep_1(A_879,B_880,C_881),A_879)
      | ~ m1_pre_topc(C_881,A_879)
      | v2_struct_0(C_881)
      | ~ m1_pre_topc(B_880,A_879)
      | v2_struct_0(B_880)
      | ~ l1_pre_topc(A_879)
      | v2_struct_0(A_879) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12047,plain,(
    ! [A_879,B_880,C_881] :
      ( m1_pre_topc(k2_tsep_1(A_879,B_880,C_881),k2_tsep_1(A_879,B_880,C_881))
      | ~ v2_pre_topc(A_879)
      | ~ m1_pre_topc(C_881,A_879)
      | v2_struct_0(C_881)
      | ~ m1_pre_topc(B_880,A_879)
      | v2_struct_0(B_880)
      | ~ l1_pre_topc(A_879)
      | v2_struct_0(A_879) ) ),
    inference(resolution,[status(thm)],[c_12029,c_674])).

tff(c_12310,plain,(
    ! [A_941,B_942,C_943] :
      ( u1_struct_0(k2_tsep_1(A_941,B_942,C_943)) = k3_xboole_0(u1_struct_0(B_942),u1_struct_0(C_943))
      | ~ m1_pre_topc(k2_tsep_1(A_941,B_942,C_943),A_941)
      | ~ v1_pre_topc(k2_tsep_1(A_941,B_942,C_943))
      | v2_struct_0(k2_tsep_1(A_941,B_942,C_943))
      | r1_tsep_1(B_942,C_943)
      | ~ m1_pre_topc(C_943,A_941)
      | v2_struct_0(C_943)
      | ~ m1_pre_topc(B_942,A_941)
      | v2_struct_0(B_942)
      | ~ l1_pre_topc(A_941)
      | v2_struct_0(A_941) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_13339,plain,(
    ! [A_997,B_998,C_999] :
      ( u1_struct_0(k2_tsep_1(A_997,B_998,C_999)) = k3_xboole_0(u1_struct_0(B_998),u1_struct_0(C_999))
      | ~ v1_pre_topc(k2_tsep_1(A_997,B_998,C_999))
      | v2_struct_0(k2_tsep_1(A_997,B_998,C_999))
      | r1_tsep_1(B_998,C_999)
      | ~ m1_pre_topc(C_999,A_997)
      | v2_struct_0(C_999)
      | ~ m1_pre_topc(B_998,A_997)
      | v2_struct_0(B_998)
      | ~ l1_pre_topc(A_997)
      | v2_struct_0(A_997) ) ),
    inference(resolution,[status(thm)],[c_38,c_12310])).

tff(c_16940,plain,(
    ! [B_1176,C_1177,A_1178] :
      ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0(B_1176),u1_struct_0(C_1177)))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1(A_1178,B_1176,C_1177))
      | ~ l1_pre_topc(k2_tsep_1(A_1178,B_1176,C_1177))
      | v2_struct_0(k2_tsep_1(A_1178,B_1176,C_1177))
      | ~ v1_pre_topc(k2_tsep_1(A_1178,B_1176,C_1177))
      | v2_struct_0(k2_tsep_1(A_1178,B_1176,C_1177))
      | r1_tsep_1(B_1176,C_1177)
      | ~ m1_pre_topc(C_1177,A_1178)
      | v2_struct_0(C_1177)
      | ~ m1_pre_topc(B_1176,A_1178)
      | v2_struct_0(B_1176)
      | ~ l1_pre_topc(A_1178)
      | v2_struct_0(A_1178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13339,c_657])).

tff(c_16943,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12047,c_16940])).

tff(c_16946,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_11707,c_16943])).

tff(c_16947,plain,
    ( m1_subset_1('#skF_4',k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_658,c_16946])).

tff(c_16948,plain,(
    ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16947])).

tff(c_16951,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_16948])).

tff(c_16954,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_16951])).

tff(c_16956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_16954])).

tff(c_16958,plain,(
    v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16947])).

tff(c_12313,plain,(
    ! [A_67,B_68,C_69] :
      ( u1_struct_0(k2_tsep_1(A_67,B_68,C_69)) = k3_xboole_0(u1_struct_0(B_68),u1_struct_0(C_69))
      | ~ v1_pre_topc(k2_tsep_1(A_67,B_68,C_69))
      | v2_struct_0(k2_tsep_1(A_67,B_68,C_69))
      | r1_tsep_1(B_68,C_69)
      | ~ m1_pre_topc(C_69,A_67)
      | v2_struct_0(C_69)
      | ~ m1_pre_topc(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_38,c_12310])).

tff(c_20187,plain,(
    ! [A_1380,B_1378,C_1379,A_1377] :
      ( u1_struct_0(k2_tsep_1(A_1380,B_1378,C_1379)) = u1_struct_0(k2_tsep_1(A_1377,B_1378,C_1379))
      | ~ v1_pre_topc(k2_tsep_1(A_1377,B_1378,C_1379))
      | v2_struct_0(k2_tsep_1(A_1377,B_1378,C_1379))
      | r1_tsep_1(B_1378,C_1379)
      | ~ m1_pre_topc(C_1379,A_1377)
      | v2_struct_0(C_1379)
      | ~ m1_pre_topc(B_1378,A_1377)
      | v2_struct_0(B_1378)
      | ~ l1_pre_topc(A_1377)
      | v2_struct_0(A_1377)
      | ~ v1_pre_topc(k2_tsep_1(A_1380,B_1378,C_1379))
      | v2_struct_0(k2_tsep_1(A_1380,B_1378,C_1379))
      | r1_tsep_1(B_1378,C_1379)
      | ~ m1_pre_topc(C_1379,A_1380)
      | v2_struct_0(C_1379)
      | ~ m1_pre_topc(B_1378,A_1380)
      | v2_struct_0(B_1378)
      | ~ l1_pre_topc(A_1380)
      | v2_struct_0(A_1380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12313,c_13339])).

tff(c_20685,plain,(
    ! [A_1380] :
      ( u1_struct_0(k2_tsep_1(A_1380,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_1380,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_1380,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1380)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1380)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1380)
      | v2_struct_0(A_1380) ) ),
    inference(resolution,[status(thm)],[c_20187,c_658])).

tff(c_20729,plain,(
    ! [A_1380] :
      ( u1_struct_0(k2_tsep_1(A_1380,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | v2_struct_0('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1(A_1380,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_1380,'#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1380)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1380)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1380)
      | v2_struct_0(A_1380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_16958,c_20685])).

tff(c_20923,plain,(
    ! [A_1391] :
      ( u1_struct_0(k2_tsep_1(A_1391,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_1391,'#skF_2','#skF_3'))
      | v2_struct_0(k2_tsep_1(A_1391,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1391)
      | ~ m1_pre_topc('#skF_2',A_1391)
      | ~ l1_pre_topc(A_1391)
      | v2_struct_0(A_1391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_66,c_20729])).

tff(c_20926,plain,(
    ! [A_1391] :
      ( v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | u1_struct_0(k2_tsep_1(A_1391,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_1391,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1391)
      | ~ m1_pre_topc('#skF_2',A_1391)
      | ~ l1_pre_topc(A_1391)
      | v2_struct_0(A_1391) ) ),
    inference(resolution,[status(thm)],[c_20923,c_42])).

tff(c_20938,plain,(
    ! [A_1392] :
      ( u1_struct_0(k2_tsep_1(A_1392,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ v1_pre_topc(k2_tsep_1(A_1392,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1392)
      | ~ m1_pre_topc('#skF_2',A_1392)
      | ~ l1_pre_topc(A_1392)
      | v2_struct_0(A_1392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_20926])).

tff(c_20945,plain,(
    ! [A_67] :
      ( u1_struct_0(k2_tsep_1(A_67,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_67)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_67)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_40,c_20938])).

tff(c_20954,plain,(
    ! [A_1393] :
      ( u1_struct_0(k2_tsep_1(A_1393,'#skF_2','#skF_3')) = u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_20945])).

tff(c_14160,plain,(
    ! [A_1027,B_1028,C_1029] :
      ( u1_struct_0(k2_tsep_1(A_1027,B_1028,C_1029)) = k3_xboole_0(u1_struct_0(B_1028),u1_struct_0(C_1029))
      | ~ v1_pre_topc(k2_tsep_1(A_1027,B_1028,C_1029))
      | r1_tsep_1(B_1028,C_1029)
      | ~ m1_pre_topc(C_1029,A_1027)
      | v2_struct_0(C_1029)
      | ~ m1_pre_topc(B_1028,A_1027)
      | v2_struct_0(B_1028)
      | ~ l1_pre_topc(A_1027)
      | v2_struct_0(A_1027) ) ),
    inference(resolution,[status(thm)],[c_13339,c_42])).

tff(c_14707,plain,(
    ! [A_1045,B_1046,C_1047] :
      ( u1_struct_0(k2_tsep_1(A_1045,B_1046,C_1047)) = k3_xboole_0(u1_struct_0(B_1046),u1_struct_0(C_1047))
      | r1_tsep_1(B_1046,C_1047)
      | ~ m1_pre_topc(C_1047,A_1045)
      | v2_struct_0(C_1047)
      | ~ m1_pre_topc(B_1046,A_1045)
      | v2_struct_0(B_1046)
      | ~ l1_pre_topc(A_1045)
      | v2_struct_0(A_1045) ) ),
    inference(resolution,[status(thm)],[c_40,c_14160])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14887,plain,(
    ! [A_1045,B_1046,C_1047] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1045,B_1046,C_1047)),u1_struct_0(B_1046))
      | r1_tsep_1(B_1046,C_1047)
      | ~ m1_pre_topc(C_1047,A_1045)
      | v2_struct_0(C_1047)
      | ~ m1_pre_topc(B_1046,A_1045)
      | v2_struct_0(B_1046)
      | ~ l1_pre_topc(A_1045)
      | v2_struct_0(A_1045) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14707,c_2])).

tff(c_21231,plain,(
    ! [A_1393] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1393,'#skF_2','#skF_3')),u1_struct_0('#skF_2'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20954,c_14887])).

tff(c_21510,plain,(
    ! [A_1393] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1393,'#skF_2','#skF_3')),u1_struct_0('#skF_2'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_21231])).

tff(c_21511,plain,(
    ! [A_1393] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1393,'#skF_2','#skF_3')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_52,c_21510])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_94])).

tff(c_103,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_116,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_664,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_659,c_116])).

tff(c_668,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_664])).

tff(c_669,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_668])).

tff(c_21237,plain,(
    ! [A_1393] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_2'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1393)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_1393)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393)
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20954,c_14887])).

tff(c_21513,plain,(
    ! [A_1393] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393)
      | ~ m1_pre_topc('#skF_3',A_1393)
      | ~ m1_pre_topc('#skF_2',A_1393)
      | ~ l1_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_21237])).

tff(c_23681,plain,(
    r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_21513])).

tff(c_23683,plain,(
    ! [A_70] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_70)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_23681,c_46])).

tff(c_23705,plain,(
    ! [A_1445] :
      ( ~ m1_pre_topc('#skF_2',A_1445)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_1445)
      | ~ l1_pre_topc(A_1445)
      | ~ v2_pre_topc(A_1445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_669,c_23683])).

tff(c_23713,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_23705])).

tff(c_23723,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_23713])).

tff(c_23725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_23723])).

tff(c_23727,plain,(
    ~ r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_21513])).

tff(c_23730,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_21511,c_23727])).

tff(c_23742,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_23730])).

tff(c_23744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_23742])).

tff(c_23745,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_24457,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24452,c_23745])).

tff(c_24461,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_24457])).

tff(c_24462,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_24461])).

tff(c_33967,plain,(
    ! [A_2181] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_2181)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2',A_2181)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181)
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33666,c_27867])).

tff(c_34213,plain,(
    ! [A_2181] :
      ( r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181)
      | ~ m1_pre_topc('#skF_3',A_2181)
      | ~ m1_pre_topc('#skF_2',A_2181)
      | ~ l1_pre_topc(A_2181)
      | v2_struct_0(A_2181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_52,c_33967])).

tff(c_35634,plain,(
    r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34213])).

tff(c_35636,plain,(
    ! [A_70] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_70)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_35634,c_46])).

tff(c_35646,plain,(
    ! [A_2225] :
      ( ~ m1_pre_topc('#skF_3',A_2225)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_2225)
      | ~ l1_pre_topc(A_2225)
      | ~ v2_pre_topc(A_2225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24462,c_35636])).

tff(c_35654,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_35646])).

tff(c_35661,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_64,c_35654])).

tff(c_35663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_56,c_35661])).

tff(c_35665,plain,(
    ~ r1_tarski(u1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34213])).

tff(c_35668,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34211,c_35665])).

tff(c_35680,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_35668])).

tff(c_35682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_35680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.38/9.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/9.79  
% 19.53/9.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.53/9.79  %$ r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.53/9.79  
% 19.53/9.79  %Foreground sorts:
% 19.53/9.79  
% 19.53/9.79  
% 19.53/9.79  %Background operators:
% 19.53/9.79  
% 19.53/9.79  
% 19.53/9.79  %Foreground operators:
% 19.53/9.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.53/9.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.53/9.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.53/9.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.53/9.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.53/9.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.53/9.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.53/9.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.53/9.79  tff('#skF_2', type, '#skF_2': $i).
% 19.53/9.79  tff('#skF_3', type, '#skF_3': $i).
% 19.53/9.79  tff('#skF_1', type, '#skF_1': $i).
% 19.53/9.79  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.53/9.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.53/9.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.53/9.79  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 19.53/9.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.53/9.79  tff('#skF_4', type, '#skF_4': $i).
% 19.53/9.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.53/9.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.53/9.79  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 19.53/9.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.53/9.79  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 19.53/9.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.53/9.79  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 19.53/9.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.53/9.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.53/9.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.53/9.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.53/9.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.53/9.79  
% 19.67/9.82  tff(f_184, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(k2_tsep_1(A, B, C))) => ((?[E]: (m1_subset_1(E, u1_struct_0(B)) & (E = D))) & (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tmap_1)).
% 19.67/9.82  tff(f_134, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 19.67/9.82  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 19.67/9.82  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 19.67/9.82  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 19.67/9.82  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.67/9.82  tff(f_148, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 19.67/9.82  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 19.67/9.82  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.67/9.82  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 19.67/9.82  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 19.67/9.82  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.67/9.82  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_58, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_52, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_40, plain, (![A_67, B_68, C_69]: (v1_pre_topc(k2_tsep_1(A_67, B_68, C_69)) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_23916, plain, (![C_1502, A_1503, B_1504]: (m1_subset_1(C_1502, u1_struct_0(A_1503)) | ~m1_subset_1(C_1502, u1_struct_0(B_1504)) | ~m1_pre_topc(B_1504, A_1503) | v2_struct_0(B_1504) | ~l1_pre_topc(A_1503) | v2_struct_0(A_1503))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.67/9.82  tff(c_23924, plain, (![A_1503]: (m1_subset_1('#skF_4', u1_struct_0(A_1503)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_1503) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_pre_topc(A_1503) | v2_struct_0(A_1503))), inference(resolution, [status(thm)], [c_50, c_23916])).
% 19.67/9.82  tff(c_23965, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_23924])).
% 19.67/9.82  tff(c_24428, plain, (![A_1575, B_1576, C_1577]: (~v2_struct_0(k2_tsep_1(A_1575, B_1576, C_1577)) | ~m1_pre_topc(C_1577, A_1575) | v2_struct_0(C_1577) | ~m1_pre_topc(B_1576, A_1575) | v2_struct_0(B_1576) | ~l1_pre_topc(A_1575) | v2_struct_0(A_1575))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_24431, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_23965, c_24428])).
% 19.67/9.82  tff(c_24434, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_24431])).
% 19.67/9.82  tff(c_24436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_24434])).
% 19.67/9.82  tff(c_24438, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_23924])).
% 19.67/9.82  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_25074, plain, (![A_1683, B_1684, C_1685]: (m1_pre_topc(k2_tsep_1(A_1683, B_1684, C_1685), A_1683) | ~m1_pre_topc(C_1685, A_1683) | v2_struct_0(C_1685) | ~m1_pre_topc(B_1684, A_1683) | v2_struct_0(B_1684) | ~l1_pre_topc(A_1683) | v2_struct_0(A_1683))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_16, plain, (![A_30]: (k2_subset_1(A_30)=A_30)), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.67/9.82  tff(c_18, plain, (![A_31]: (m1_subset_1(k2_subset_1(A_31), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.67/9.82  tff(c_67, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 19.67/9.82  tff(c_88, plain, (![A_126, B_127]: (r1_tarski(A_126, B_127) | ~m1_subset_1(A_126, k1_zfmisc_1(B_127)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.67/9.82  tff(c_92, plain, (![A_31]: (r1_tarski(A_31, A_31))), inference(resolution, [status(thm)], [c_67, c_88])).
% 19.67/9.82  tff(c_24794, plain, (![B_1627, C_1628, A_1629]: (m1_pre_topc(B_1627, C_1628) | ~r1_tarski(u1_struct_0(B_1627), u1_struct_0(C_1628)) | ~m1_pre_topc(C_1628, A_1629) | ~m1_pre_topc(B_1627, A_1629) | ~l1_pre_topc(A_1629) | ~v2_pre_topc(A_1629))), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.67/9.82  tff(c_24804, plain, (![B_1627, A_1629]: (m1_pre_topc(B_1627, B_1627) | ~m1_pre_topc(B_1627, A_1629) | ~l1_pre_topc(A_1629) | ~v2_pre_topc(A_1629))), inference(resolution, [status(thm)], [c_92, c_24794])).
% 19.67/9.82  tff(c_25090, plain, (![A_1683, B_1684, C_1685]: (m1_pre_topc(k2_tsep_1(A_1683, B_1684, C_1685), k2_tsep_1(A_1683, B_1684, C_1685)) | ~v2_pre_topc(A_1683) | ~m1_pre_topc(C_1685, A_1683) | v2_struct_0(C_1685) | ~m1_pre_topc(B_1684, A_1683) | v2_struct_0(B_1684) | ~l1_pre_topc(A_1683) | v2_struct_0(A_1683))), inference(resolution, [status(thm)], [c_25074, c_24804])).
% 19.67/9.82  tff(c_38, plain, (![A_67, B_68, C_69]: (m1_pre_topc(k2_tsep_1(A_67, B_68, C_69), A_67) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_25300, plain, (![A_1734, B_1735, C_1736]: (u1_struct_0(k2_tsep_1(A_1734, B_1735, C_1736))=k3_xboole_0(u1_struct_0(B_1735), u1_struct_0(C_1736)) | ~m1_pre_topc(k2_tsep_1(A_1734, B_1735, C_1736), A_1734) | ~v1_pre_topc(k2_tsep_1(A_1734, B_1735, C_1736)) | v2_struct_0(k2_tsep_1(A_1734, B_1735, C_1736)) | r1_tsep_1(B_1735, C_1736) | ~m1_pre_topc(C_1736, A_1734) | v2_struct_0(C_1736) | ~m1_pre_topc(B_1735, A_1734) | v2_struct_0(B_1735) | ~l1_pre_topc(A_1734) | v2_struct_0(A_1734))), inference(cnfTransformation, [status(thm)], [f_112])).
% 19.67/9.82  tff(c_26511, plain, (![A_1799, B_1800, C_1801]: (u1_struct_0(k2_tsep_1(A_1799, B_1800, C_1801))=k3_xboole_0(u1_struct_0(B_1800), u1_struct_0(C_1801)) | ~v1_pre_topc(k2_tsep_1(A_1799, B_1800, C_1801)) | v2_struct_0(k2_tsep_1(A_1799, B_1800, C_1801)) | r1_tsep_1(B_1800, C_1801) | ~m1_pre_topc(C_1801, A_1799) | v2_struct_0(C_1801) | ~m1_pre_topc(B_1800, A_1799) | v2_struct_0(B_1800) | ~l1_pre_topc(A_1799) | v2_struct_0(A_1799))), inference(resolution, [status(thm)], [c_38, c_25300])).
% 19.67/9.82  tff(c_24437, plain, (![A_1503]: (m1_subset_1('#skF_4', u1_struct_0(A_1503)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_1503) | ~l1_pre_topc(A_1503) | v2_struct_0(A_1503))), inference(splitRight, [status(thm)], [c_23924])).
% 19.67/9.82  tff(c_30046, plain, (![B_1975, C_1976, A_1977]: (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0(B_1975), u1_struct_0(C_1976))) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1(A_1977, B_1975, C_1976)) | ~l1_pre_topc(k2_tsep_1(A_1977, B_1975, C_1976)) | v2_struct_0(k2_tsep_1(A_1977, B_1975, C_1976)) | ~v1_pre_topc(k2_tsep_1(A_1977, B_1975, C_1976)) | v2_struct_0(k2_tsep_1(A_1977, B_1975, C_1976)) | r1_tsep_1(B_1975, C_1976) | ~m1_pre_topc(C_1976, A_1977) | v2_struct_0(C_1976) | ~m1_pre_topc(B_1975, A_1977) | v2_struct_0(B_1975) | ~l1_pre_topc(A_1977) | v2_struct_0(A_1977))), inference(superposition, [status(thm), theory('equality')], [c_26511, c_24437])).
% 19.67/9.82  tff(c_30049, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_25090, c_30046])).
% 19.67/9.82  tff(c_30052, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_30049])).
% 19.67/9.82  tff(c_30053, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_24438, c_30052])).
% 19.67/9.82  tff(c_30054, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_30053])).
% 19.67/9.82  tff(c_30057, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_30054])).
% 19.67/9.82  tff(c_30060, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_30057])).
% 19.67/9.82  tff(c_30062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_30060])).
% 19.67/9.82  tff(c_30064, plain, (v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_30053])).
% 19.67/9.82  tff(c_25303, plain, (![A_67, B_68, C_69]: (u1_struct_0(k2_tsep_1(A_67, B_68, C_69))=k3_xboole_0(u1_struct_0(B_68), u1_struct_0(C_69)) | ~v1_pre_topc(k2_tsep_1(A_67, B_68, C_69)) | v2_struct_0(k2_tsep_1(A_67, B_68, C_69)) | r1_tsep_1(B_68, C_69) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_38, c_25300])).
% 19.67/9.82  tff(c_33004, plain, (![A_2173, B_2171, C_2172, A_2170]: (u1_struct_0(k2_tsep_1(A_2173, B_2171, C_2172))=u1_struct_0(k2_tsep_1(A_2170, B_2171, C_2172)) | ~v1_pre_topc(k2_tsep_1(A_2173, B_2171, C_2172)) | v2_struct_0(k2_tsep_1(A_2173, B_2171, C_2172)) | r1_tsep_1(B_2171, C_2172) | ~m1_pre_topc(C_2172, A_2173) | v2_struct_0(C_2172) | ~m1_pre_topc(B_2171, A_2173) | v2_struct_0(B_2171) | ~l1_pre_topc(A_2173) | v2_struct_0(A_2173) | ~v1_pre_topc(k2_tsep_1(A_2170, B_2171, C_2172)) | v2_struct_0(k2_tsep_1(A_2170, B_2171, C_2172)) | r1_tsep_1(B_2171, C_2172) | ~m1_pre_topc(C_2172, A_2170) | v2_struct_0(C_2172) | ~m1_pre_topc(B_2171, A_2170) | v2_struct_0(B_2171) | ~l1_pre_topc(A_2170) | v2_struct_0(A_2170))), inference(superposition, [status(thm), theory('equality')], [c_25303, c_26511])).
% 19.67/9.82  tff(c_33508, plain, (![A_2170]: (u1_struct_0(k2_tsep_1(A_2170, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_2170, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_2170, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_2170) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_2170) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_2170) | v2_struct_0(A_2170))), inference(resolution, [status(thm)], [c_33004, c_24438])).
% 19.67/9.82  tff(c_33552, plain, (![A_2170]: (u1_struct_0(k2_tsep_1(A_2170, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_2170, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_2170, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_2170) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_2170) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_2170) | v2_struct_0(A_2170))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_30064, c_33508])).
% 19.67/9.82  tff(c_33635, plain, (![A_2179]: (u1_struct_0(k2_tsep_1(A_2179, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_2179, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_2179, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_2179) | ~m1_pre_topc('#skF_2', A_2179) | ~l1_pre_topc(A_2179) | v2_struct_0(A_2179))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_66, c_33552])).
% 19.67/9.82  tff(c_42, plain, (![A_67, B_68, C_69]: (~v2_struct_0(k2_tsep_1(A_67, B_68, C_69)) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_33638, plain, (![A_2179]: (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | u1_struct_0(k2_tsep_1(A_2179, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_2179, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_2179) | ~m1_pre_topc('#skF_2', A_2179) | ~l1_pre_topc(A_2179) | v2_struct_0(A_2179))), inference(resolution, [status(thm)], [c_33635, c_42])).
% 19.67/9.82  tff(c_33650, plain, (![A_2180]: (u1_struct_0(k2_tsep_1(A_2180, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_2180, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_2180) | ~m1_pre_topc('#skF_2', A_2180) | ~l1_pre_topc(A_2180) | v2_struct_0(A_2180))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_33638])).
% 19.67/9.82  tff(c_33657, plain, (![A_67]: (u1_struct_0(k2_tsep_1(A_67, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_67) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_67) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_40, c_33650])).
% 19.67/9.82  tff(c_33666, plain, (![A_2181]: (u1_struct_0(k2_tsep_1(A_2181, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_33657])).
% 19.67/9.82  tff(c_27689, plain, (![A_1832, B_1833, C_1834]: (u1_struct_0(k2_tsep_1(A_1832, B_1833, C_1834))=k3_xboole_0(u1_struct_0(B_1833), u1_struct_0(C_1834)) | ~v1_pre_topc(k2_tsep_1(A_1832, B_1833, C_1834)) | r1_tsep_1(B_1833, C_1834) | ~m1_pre_topc(C_1834, A_1832) | v2_struct_0(C_1834) | ~m1_pre_topc(B_1833, A_1832) | v2_struct_0(B_1833) | ~l1_pre_topc(A_1832) | v2_struct_0(A_1832))), inference(resolution, [status(thm)], [c_26511, c_42])).
% 19.67/9.82  tff(c_27693, plain, (![A_1835, B_1836, C_1837]: (u1_struct_0(k2_tsep_1(A_1835, B_1836, C_1837))=k3_xboole_0(u1_struct_0(B_1836), u1_struct_0(C_1837)) | r1_tsep_1(B_1836, C_1837) | ~m1_pre_topc(C_1837, A_1835) | v2_struct_0(C_1837) | ~m1_pre_topc(B_1836, A_1835) | v2_struct_0(B_1836) | ~l1_pre_topc(A_1835) | v2_struct_0(A_1835))), inference(resolution, [status(thm)], [c_40, c_27689])).
% 19.67/9.82  tff(c_23761, plain, (![A_1451, B_1452, C_1453]: (k9_subset_1(A_1451, B_1452, C_1453)=k3_xboole_0(B_1452, C_1453) | ~m1_subset_1(C_1453, k1_zfmisc_1(A_1451)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.67/9.82  tff(c_23767, plain, (![A_31, B_1452]: (k9_subset_1(A_31, B_1452, A_31)=k3_xboole_0(B_1452, A_31))), inference(resolution, [status(thm)], [c_67, c_23761])).
% 19.67/9.82  tff(c_23794, plain, (![A_1463, B_1464, C_1465]: (m1_subset_1(k9_subset_1(A_1463, B_1464, C_1465), k1_zfmisc_1(A_1463)) | ~m1_subset_1(C_1465, k1_zfmisc_1(A_1463)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.67/9.82  tff(c_23802, plain, (![B_1452, A_31]: (m1_subset_1(k3_xboole_0(B_1452, A_31), k1_zfmisc_1(A_31)) | ~m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_23767, c_23794])).
% 19.67/9.82  tff(c_23807, plain, (![B_1466, A_1467]: (m1_subset_1(k3_xboole_0(B_1466, A_1467), k1_zfmisc_1(A_1467)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_23802])).
% 19.67/9.82  tff(c_26, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.67/9.82  tff(c_23814, plain, (![B_1466, A_1467]: (r1_tarski(k3_xboole_0(B_1466, A_1467), A_1467))), inference(resolution, [status(thm)], [c_23807, c_26])).
% 19.67/9.82  tff(c_27867, plain, (![A_1835, B_1836, C_1837]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1835, B_1836, C_1837)), u1_struct_0(C_1837)) | r1_tsep_1(B_1836, C_1837) | ~m1_pre_topc(C_1837, A_1835) | v2_struct_0(C_1837) | ~m1_pre_topc(B_1836, A_1835) | v2_struct_0(B_1836) | ~l1_pre_topc(A_1835) | v2_struct_0(A_1835))), inference(superposition, [status(thm), theory('equality')], [c_27693, c_23814])).
% 19.67/9.82  tff(c_33961, plain, (![A_2181]: (r1_tarski(u1_struct_0(k2_tsep_1(A_2181, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(superposition, [status(thm), theory('equality')], [c_33666, c_27867])).
% 19.67/9.82  tff(c_34210, plain, (![A_2181]: (r1_tarski(u1_struct_0(k2_tsep_1(A_2181, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_33961])).
% 19.67/9.82  tff(c_34211, plain, (![A_2181]: (r1_tarski(u1_struct_0(k2_tsep_1(A_2181, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_34210])).
% 19.67/9.82  tff(c_94, plain, (![B_129, A_130]: (l1_pre_topc(B_129) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.67/9.82  tff(c_100, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_94])).
% 19.67/9.82  tff(c_106, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_100])).
% 19.67/9.82  tff(c_24452, plain, (![A_1586]: (m1_subset_1('#skF_4', u1_struct_0(A_1586)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_1586) | ~l1_pre_topc(A_1586) | v2_struct_0(A_1586))), inference(splitRight, [status(thm)], [c_23924])).
% 19.67/9.82  tff(c_329, plain, (![C_201, A_202, B_203]: (m1_subset_1(C_201, u1_struct_0(A_202)) | ~m1_subset_1(C_201, u1_struct_0(B_203)) | ~m1_pre_topc(B_203, A_202) | v2_struct_0(B_203) | ~l1_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.67/9.82  tff(c_332, plain, (![A_202]: (m1_subset_1('#skF_4', u1_struct_0(A_202)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_202) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_pre_topc(A_202) | v2_struct_0(A_202))), inference(resolution, [status(thm)], [c_50, c_329])).
% 19.67/9.82  tff(c_447, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_332])).
% 19.67/9.82  tff(c_648, plain, (![A_259, B_260, C_261]: (~v2_struct_0(k2_tsep_1(A_259, B_260, C_261)) | ~m1_pre_topc(C_261, A_259) | v2_struct_0(C_261) | ~m1_pre_topc(B_260, A_259) | v2_struct_0(B_260) | ~l1_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_651, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_447, c_648])).
% 19.67/9.82  tff(c_654, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_651])).
% 19.67/9.82  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_654])).
% 19.67/9.82  tff(c_658, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_332])).
% 19.67/9.82  tff(c_1015, plain, (![A_326, B_327, C_328]: (m1_pre_topc(k2_tsep_1(A_326, B_327, C_328), A_326) | ~m1_pre_topc(C_328, A_326) | v2_struct_0(C_328) | ~m1_pre_topc(B_327, A_326) | v2_struct_0(B_327) | ~l1_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_670, plain, (![B_263, C_264, A_265]: (m1_pre_topc(B_263, C_264) | ~r1_tarski(u1_struct_0(B_263), u1_struct_0(C_264)) | ~m1_pre_topc(C_264, A_265) | ~m1_pre_topc(B_263, A_265) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.67/9.82  tff(c_674, plain, (![B_263, A_265]: (m1_pre_topc(B_263, B_263) | ~m1_pre_topc(B_263, A_265) | ~l1_pre_topc(A_265) | ~v2_pre_topc(A_265))), inference(resolution, [status(thm)], [c_92, c_670])).
% 19.67/9.82  tff(c_1027, plain, (![A_326, B_327, C_328]: (m1_pre_topc(k2_tsep_1(A_326, B_327, C_328), k2_tsep_1(A_326, B_327, C_328)) | ~v2_pre_topc(A_326) | ~m1_pre_topc(C_328, A_326) | v2_struct_0(C_328) | ~m1_pre_topc(B_327, A_326) | v2_struct_0(B_327) | ~l1_pre_topc(A_326) | v2_struct_0(A_326))), inference(resolution, [status(thm)], [c_1015, c_674])).
% 19.67/9.82  tff(c_1370, plain, (![A_379, B_380, C_381]: (u1_struct_0(k2_tsep_1(A_379, B_380, C_381))=k3_xboole_0(u1_struct_0(B_380), u1_struct_0(C_381)) | ~m1_pre_topc(k2_tsep_1(A_379, B_380, C_381), A_379) | ~v1_pre_topc(k2_tsep_1(A_379, B_380, C_381)) | v2_struct_0(k2_tsep_1(A_379, B_380, C_381)) | r1_tsep_1(B_380, C_381) | ~m1_pre_topc(C_381, A_379) | v2_struct_0(C_381) | ~m1_pre_topc(B_380, A_379) | v2_struct_0(B_380) | ~l1_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_112])).
% 19.67/9.82  tff(c_2454, plain, (![A_439, B_440, C_441]: (u1_struct_0(k2_tsep_1(A_439, B_440, C_441))=k3_xboole_0(u1_struct_0(B_440), u1_struct_0(C_441)) | ~v1_pre_topc(k2_tsep_1(A_439, B_440, C_441)) | v2_struct_0(k2_tsep_1(A_439, B_440, C_441)) | r1_tsep_1(B_440, C_441) | ~m1_pre_topc(C_441, A_439) | v2_struct_0(C_441) | ~m1_pre_topc(B_440, A_439) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | v2_struct_0(A_439))), inference(resolution, [status(thm)], [c_38, c_1370])).
% 19.67/9.82  tff(c_657, plain, (![A_202]: (m1_subset_1('#skF_4', u1_struct_0(A_202)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_202) | ~l1_pre_topc(A_202) | v2_struct_0(A_202))), inference(splitRight, [status(thm)], [c_332])).
% 19.67/9.82  tff(c_5437, plain, (![B_587, C_588, A_589]: (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0(B_587), u1_struct_0(C_588))) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1(A_589, B_587, C_588)) | ~l1_pre_topc(k2_tsep_1(A_589, B_587, C_588)) | v2_struct_0(k2_tsep_1(A_589, B_587, C_588)) | ~v1_pre_topc(k2_tsep_1(A_589, B_587, C_588)) | v2_struct_0(k2_tsep_1(A_589, B_587, C_588)) | r1_tsep_1(B_587, C_588) | ~m1_pre_topc(C_588, A_589) | v2_struct_0(C_588) | ~m1_pre_topc(B_587, A_589) | v2_struct_0(B_587) | ~l1_pre_topc(A_589) | v2_struct_0(A_589))), inference(superposition, [status(thm), theory('equality')], [c_2454, c_657])).
% 19.67/9.82  tff(c_5440, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1027, c_5437])).
% 19.67/9.82  tff(c_5443, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_5440])).
% 19.67/9.82  tff(c_5444, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_658, c_5443])).
% 19.67/9.82  tff(c_5445, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5444])).
% 19.67/9.82  tff(c_5448, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_5445])).
% 19.67/9.82  tff(c_5451, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_5448])).
% 19.67/9.82  tff(c_5453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_5451])).
% 19.67/9.82  tff(c_5455, plain, (v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_5444])).
% 19.67/9.82  tff(c_1373, plain, (![A_67, B_68, C_69]: (u1_struct_0(k2_tsep_1(A_67, B_68, C_69))=k3_xboole_0(u1_struct_0(B_68), u1_struct_0(C_69)) | ~v1_pre_topc(k2_tsep_1(A_67, B_68, C_69)) | v2_struct_0(k2_tsep_1(A_67, B_68, C_69)) | r1_tsep_1(B_68, C_69) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_38, c_1370])).
% 19.67/9.82  tff(c_8809, plain, (![A_779, B_777, C_778, A_776]: (u1_struct_0(k2_tsep_1(A_779, B_777, C_778))=u1_struct_0(k2_tsep_1(A_776, B_777, C_778)) | ~v1_pre_topc(k2_tsep_1(A_779, B_777, C_778)) | v2_struct_0(k2_tsep_1(A_779, B_777, C_778)) | r1_tsep_1(B_777, C_778) | ~m1_pre_topc(C_778, A_779) | v2_struct_0(C_778) | ~m1_pre_topc(B_777, A_779) | v2_struct_0(B_777) | ~l1_pre_topc(A_779) | v2_struct_0(A_779) | ~v1_pre_topc(k2_tsep_1(A_776, B_777, C_778)) | v2_struct_0(k2_tsep_1(A_776, B_777, C_778)) | r1_tsep_1(B_777, C_778) | ~m1_pre_topc(C_778, A_776) | v2_struct_0(C_778) | ~m1_pre_topc(B_777, A_776) | v2_struct_0(B_777) | ~l1_pre_topc(A_776) | v2_struct_0(A_776))), inference(superposition, [status(thm), theory('equality')], [c_1373, c_2454])).
% 19.67/9.82  tff(c_9299, plain, (![A_776]: (u1_struct_0(k2_tsep_1(A_776, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_776, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_776, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_776) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_776) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_776) | v2_struct_0(A_776))), inference(resolution, [status(thm)], [c_8809, c_658])).
% 19.67/9.82  tff(c_9343, plain, (![A_776]: (u1_struct_0(k2_tsep_1(A_776, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_776, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_776, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_776) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_776) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_776) | v2_struct_0(A_776))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_5455, c_9299])).
% 19.67/9.82  tff(c_9572, plain, (![A_785]: (u1_struct_0(k2_tsep_1(A_785, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_785, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_785, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_785) | ~m1_pre_topc('#skF_2', A_785) | ~l1_pre_topc(A_785) | v2_struct_0(A_785))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_66, c_9343])).
% 19.67/9.82  tff(c_9575, plain, (![A_785]: (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | u1_struct_0(k2_tsep_1(A_785, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_785, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_785) | ~m1_pre_topc('#skF_2', A_785) | ~l1_pre_topc(A_785) | v2_struct_0(A_785))), inference(resolution, [status(thm)], [c_9572, c_42])).
% 19.67/9.82  tff(c_9587, plain, (![A_786]: (u1_struct_0(k2_tsep_1(A_786, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_786, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_786) | ~m1_pre_topc('#skF_2', A_786) | ~l1_pre_topc(A_786) | v2_struct_0(A_786))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_9575])).
% 19.67/9.82  tff(c_9594, plain, (![A_67]: (u1_struct_0(k2_tsep_1(A_67, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_67) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_67) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_40, c_9587])).
% 19.67/9.82  tff(c_9603, plain, (![A_787]: (u1_struct_0(k2_tsep_1(A_787, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_9594])).
% 19.67/9.82  tff(c_3476, plain, (![A_471, B_472, C_473]: (u1_struct_0(k2_tsep_1(A_471, B_472, C_473))=k3_xboole_0(u1_struct_0(B_472), u1_struct_0(C_473)) | ~v1_pre_topc(k2_tsep_1(A_471, B_472, C_473)) | r1_tsep_1(B_472, C_473) | ~m1_pre_topc(C_473, A_471) | v2_struct_0(C_473) | ~m1_pre_topc(B_472, A_471) | v2_struct_0(B_472) | ~l1_pre_topc(A_471) | v2_struct_0(A_471))), inference(resolution, [status(thm)], [c_2454, c_42])).
% 19.67/9.82  tff(c_3649, plain, (![A_478, B_479, C_480]: (u1_struct_0(k2_tsep_1(A_478, B_479, C_480))=k3_xboole_0(u1_struct_0(B_479), u1_struct_0(C_480)) | r1_tsep_1(B_479, C_480) | ~m1_pre_topc(C_480, A_478) | v2_struct_0(C_480) | ~m1_pre_topc(B_479, A_478) | v2_struct_0(B_479) | ~l1_pre_topc(A_478) | v2_struct_0(A_478))), inference(resolution, [status(thm)], [c_40, c_3476])).
% 19.67/9.82  tff(c_131, plain, (![A_138, B_139, C_140]: (k9_subset_1(A_138, B_139, C_140)=k3_xboole_0(B_139, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.67/9.82  tff(c_137, plain, (![A_31, B_139]: (k9_subset_1(A_31, B_139, A_31)=k3_xboole_0(B_139, A_31))), inference(resolution, [status(thm)], [c_67, c_131])).
% 19.67/9.82  tff(c_147, plain, (![A_143, B_144, C_145]: (m1_subset_1(k9_subset_1(A_143, B_144, C_145), k1_zfmisc_1(A_143)) | ~m1_subset_1(C_145, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.67/9.82  tff(c_155, plain, (![B_139, A_31]: (m1_subset_1(k3_xboole_0(B_139, A_31), k1_zfmisc_1(A_31)) | ~m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_147])).
% 19.67/9.82  tff(c_160, plain, (![B_146, A_147]: (m1_subset_1(k3_xboole_0(B_146, A_147), k1_zfmisc_1(A_147)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_155])).
% 19.67/9.82  tff(c_167, plain, (![B_146, A_147]: (r1_tarski(k3_xboole_0(B_146, A_147), A_147))), inference(resolution, [status(thm)], [c_160, c_26])).
% 19.67/9.82  tff(c_3825, plain, (![A_478, B_479, C_480]: (r1_tarski(u1_struct_0(k2_tsep_1(A_478, B_479, C_480)), u1_struct_0(C_480)) | r1_tsep_1(B_479, C_480) | ~m1_pre_topc(C_480, A_478) | v2_struct_0(C_480) | ~m1_pre_topc(B_479, A_478) | v2_struct_0(B_479) | ~l1_pre_topc(A_478) | v2_struct_0(A_478))), inference(superposition, [status(thm), theory('equality')], [c_3649, c_167])).
% 19.67/9.82  tff(c_9862, plain, (![A_787]: (r1_tarski(u1_struct_0(k2_tsep_1(A_787, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(superposition, [status(thm), theory('equality')], [c_9603, c_3825])).
% 19.67/9.82  tff(c_10127, plain, (![A_787]: (r1_tarski(u1_struct_0(k2_tsep_1(A_787, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_9862])).
% 19.67/9.82  tff(c_10128, plain, (![A_787]: (r1_tarski(u1_struct_0(k2_tsep_1(A_787, '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_10127])).
% 19.67/9.82  tff(c_659, plain, (![A_262]: (m1_subset_1('#skF_4', u1_struct_0(A_262)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_262) | ~l1_pre_topc(A_262) | v2_struct_0(A_262))), inference(splitRight, [status(thm)], [c_332])).
% 19.67/9.82  tff(c_32, plain, (![C_51, A_45, B_49]: (m1_subset_1(C_51, u1_struct_0(A_45)) | ~m1_subset_1(C_51, u1_struct_0(B_49)) | ~m1_pre_topc(B_49, A_45) | v2_struct_0(B_49) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.67/9.82  tff(c_708, plain, (![A_268, A_269]: (m1_subset_1('#skF_4', u1_struct_0(A_268)) | ~m1_pre_topc(A_269, A_268) | ~l1_pre_topc(A_268) | v2_struct_0(A_268) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_269) | ~l1_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_659, c_32])).
% 19.67/9.82  tff(c_716, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_708])).
% 19.67/9.82  tff(c_731, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | v2_struct_0('#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_62, c_716])).
% 19.67/9.82  tff(c_732, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_66, c_731])).
% 19.67/9.82  tff(c_733, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_732])).
% 19.67/9.82  tff(c_9868, plain, (![A_787]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_787) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_787) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_787) | v2_struct_0(A_787) | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(superposition, [status(thm), theory('equality')], [c_9603, c_3825])).
% 19.67/9.82  tff(c_10130, plain, (![A_787]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787) | ~m1_pre_topc('#skF_3', A_787) | ~m1_pre_topc('#skF_2', A_787) | ~l1_pre_topc(A_787) | v2_struct_0(A_787))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_9868])).
% 19.67/9.82  tff(c_11635, plain, (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_10130])).
% 19.67/9.82  tff(c_46, plain, (![B_74, C_76, A_70]: (m1_pre_topc(B_74, C_76) | ~r1_tarski(u1_struct_0(B_74), u1_struct_0(C_76)) | ~m1_pre_topc(C_76, A_70) | ~m1_pre_topc(B_74, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.67/9.82  tff(c_11637, plain, (![A_70]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', A_70) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(resolution, [status(thm)], [c_11635, c_46])).
% 19.67/9.82  tff(c_11647, plain, (![A_827]: (~m1_pre_topc('#skF_3', A_827) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_827) | ~l1_pre_topc(A_827) | ~v2_pre_topc(A_827))), inference(negUnitSimplification, [status(thm)], [c_733, c_11637])).
% 19.67/9.82  tff(c_11655, plain, (~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_11647])).
% 19.67/9.82  tff(c_11662, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_11655])).
% 19.67/9.82  tff(c_11664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_11662])).
% 19.67/9.82  tff(c_11666, plain, (~r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_10130])).
% 19.67/9.82  tff(c_11669, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10128, c_11666])).
% 19.67/9.82  tff(c_11681, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_11669])).
% 19.67/9.82  tff(c_11683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_11681])).
% 19.67/9.82  tff(c_11685, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_732])).
% 19.67/9.82  tff(c_30, plain, (![B_44, A_42]: (l1_pre_topc(B_44) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.67/9.82  tff(c_11697, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_11685, c_30])).
% 19.67/9.82  tff(c_11707, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_11697])).
% 19.67/9.82  tff(c_12029, plain, (![A_879, B_880, C_881]: (m1_pre_topc(k2_tsep_1(A_879, B_880, C_881), A_879) | ~m1_pre_topc(C_881, A_879) | v2_struct_0(C_881) | ~m1_pre_topc(B_880, A_879) | v2_struct_0(B_880) | ~l1_pre_topc(A_879) | v2_struct_0(A_879))), inference(cnfTransformation, [status(thm)], [f_134])).
% 19.67/9.82  tff(c_12047, plain, (![A_879, B_880, C_881]: (m1_pre_topc(k2_tsep_1(A_879, B_880, C_881), k2_tsep_1(A_879, B_880, C_881)) | ~v2_pre_topc(A_879) | ~m1_pre_topc(C_881, A_879) | v2_struct_0(C_881) | ~m1_pre_topc(B_880, A_879) | v2_struct_0(B_880) | ~l1_pre_topc(A_879) | v2_struct_0(A_879))), inference(resolution, [status(thm)], [c_12029, c_674])).
% 19.67/9.82  tff(c_12310, plain, (![A_941, B_942, C_943]: (u1_struct_0(k2_tsep_1(A_941, B_942, C_943))=k3_xboole_0(u1_struct_0(B_942), u1_struct_0(C_943)) | ~m1_pre_topc(k2_tsep_1(A_941, B_942, C_943), A_941) | ~v1_pre_topc(k2_tsep_1(A_941, B_942, C_943)) | v2_struct_0(k2_tsep_1(A_941, B_942, C_943)) | r1_tsep_1(B_942, C_943) | ~m1_pre_topc(C_943, A_941) | v2_struct_0(C_943) | ~m1_pre_topc(B_942, A_941) | v2_struct_0(B_942) | ~l1_pre_topc(A_941) | v2_struct_0(A_941))), inference(cnfTransformation, [status(thm)], [f_112])).
% 19.67/9.82  tff(c_13339, plain, (![A_997, B_998, C_999]: (u1_struct_0(k2_tsep_1(A_997, B_998, C_999))=k3_xboole_0(u1_struct_0(B_998), u1_struct_0(C_999)) | ~v1_pre_topc(k2_tsep_1(A_997, B_998, C_999)) | v2_struct_0(k2_tsep_1(A_997, B_998, C_999)) | r1_tsep_1(B_998, C_999) | ~m1_pre_topc(C_999, A_997) | v2_struct_0(C_999) | ~m1_pre_topc(B_998, A_997) | v2_struct_0(B_998) | ~l1_pre_topc(A_997) | v2_struct_0(A_997))), inference(resolution, [status(thm)], [c_38, c_12310])).
% 19.67/9.82  tff(c_16940, plain, (![B_1176, C_1177, A_1178]: (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0(B_1176), u1_struct_0(C_1177))) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1(A_1178, B_1176, C_1177)) | ~l1_pre_topc(k2_tsep_1(A_1178, B_1176, C_1177)) | v2_struct_0(k2_tsep_1(A_1178, B_1176, C_1177)) | ~v1_pre_topc(k2_tsep_1(A_1178, B_1176, C_1177)) | v2_struct_0(k2_tsep_1(A_1178, B_1176, C_1177)) | r1_tsep_1(B_1176, C_1177) | ~m1_pre_topc(C_1177, A_1178) | v2_struct_0(C_1177) | ~m1_pre_topc(B_1176, A_1178) | v2_struct_0(B_1176) | ~l1_pre_topc(A_1178) | v2_struct_0(A_1178))), inference(superposition, [status(thm), theory('equality')], [c_13339, c_657])).
% 19.67/9.82  tff(c_16943, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12047, c_16940])).
% 19.67/9.82  tff(c_16946, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_11707, c_16943])).
% 19.67/9.82  tff(c_16947, plain, (m1_subset_1('#skF_4', k3_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_658, c_16946])).
% 19.67/9.82  tff(c_16948, plain, (~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_16947])).
% 19.67/9.82  tff(c_16951, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_16948])).
% 19.67/9.82  tff(c_16954, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_16951])).
% 19.67/9.82  tff(c_16956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_16954])).
% 19.67/9.82  tff(c_16958, plain, (v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_16947])).
% 19.67/9.82  tff(c_12313, plain, (![A_67, B_68, C_69]: (u1_struct_0(k2_tsep_1(A_67, B_68, C_69))=k3_xboole_0(u1_struct_0(B_68), u1_struct_0(C_69)) | ~v1_pre_topc(k2_tsep_1(A_67, B_68, C_69)) | v2_struct_0(k2_tsep_1(A_67, B_68, C_69)) | r1_tsep_1(B_68, C_69) | ~m1_pre_topc(C_69, A_67) | v2_struct_0(C_69) | ~m1_pre_topc(B_68, A_67) | v2_struct_0(B_68) | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_38, c_12310])).
% 19.67/9.82  tff(c_20187, plain, (![A_1380, B_1378, C_1379, A_1377]: (u1_struct_0(k2_tsep_1(A_1380, B_1378, C_1379))=u1_struct_0(k2_tsep_1(A_1377, B_1378, C_1379)) | ~v1_pre_topc(k2_tsep_1(A_1377, B_1378, C_1379)) | v2_struct_0(k2_tsep_1(A_1377, B_1378, C_1379)) | r1_tsep_1(B_1378, C_1379) | ~m1_pre_topc(C_1379, A_1377) | v2_struct_0(C_1379) | ~m1_pre_topc(B_1378, A_1377) | v2_struct_0(B_1378) | ~l1_pre_topc(A_1377) | v2_struct_0(A_1377) | ~v1_pre_topc(k2_tsep_1(A_1380, B_1378, C_1379)) | v2_struct_0(k2_tsep_1(A_1380, B_1378, C_1379)) | r1_tsep_1(B_1378, C_1379) | ~m1_pre_topc(C_1379, A_1380) | v2_struct_0(C_1379) | ~m1_pre_topc(B_1378, A_1380) | v2_struct_0(B_1378) | ~l1_pre_topc(A_1380) | v2_struct_0(A_1380))), inference(superposition, [status(thm), theory('equality')], [c_12313, c_13339])).
% 19.67/9.82  tff(c_20685, plain, (![A_1380]: (u1_struct_0(k2_tsep_1(A_1380, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_1380, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_1380, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1380) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1380) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1380) | v2_struct_0(A_1380))), inference(resolution, [status(thm)], [c_20187, c_658])).
% 19.67/9.82  tff(c_20729, plain, (![A_1380]: (u1_struct_0(k2_tsep_1(A_1380, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0('#skF_1') | ~v1_pre_topc(k2_tsep_1(A_1380, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_1380, '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1380) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1380) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1380) | v2_struct_0(A_1380))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_16958, c_20685])).
% 19.67/9.82  tff(c_20923, plain, (![A_1391]: (u1_struct_0(k2_tsep_1(A_1391, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_1391, '#skF_2', '#skF_3')) | v2_struct_0(k2_tsep_1(A_1391, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1391) | ~m1_pre_topc('#skF_2', A_1391) | ~l1_pre_topc(A_1391) | v2_struct_0(A_1391))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_66, c_20729])).
% 19.67/9.82  tff(c_20926, plain, (![A_1391]: (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | u1_struct_0(k2_tsep_1(A_1391, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_1391, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1391) | ~m1_pre_topc('#skF_2', A_1391) | ~l1_pre_topc(A_1391) | v2_struct_0(A_1391))), inference(resolution, [status(thm)], [c_20923, c_42])).
% 19.67/9.82  tff(c_20938, plain, (![A_1392]: (u1_struct_0(k2_tsep_1(A_1392, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~v1_pre_topc(k2_tsep_1(A_1392, '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1392) | ~m1_pre_topc('#skF_2', A_1392) | ~l1_pre_topc(A_1392) | v2_struct_0(A_1392))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_20926])).
% 19.67/9.82  tff(c_20945, plain, (![A_67]: (u1_struct_0(k2_tsep_1(A_67, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_67) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_67) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_40, c_20938])).
% 19.67/9.82  tff(c_20954, plain, (![A_1393]: (u1_struct_0(k2_tsep_1(A_1393, '#skF_2', '#skF_3'))=u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_20945])).
% 19.67/9.82  tff(c_14160, plain, (![A_1027, B_1028, C_1029]: (u1_struct_0(k2_tsep_1(A_1027, B_1028, C_1029))=k3_xboole_0(u1_struct_0(B_1028), u1_struct_0(C_1029)) | ~v1_pre_topc(k2_tsep_1(A_1027, B_1028, C_1029)) | r1_tsep_1(B_1028, C_1029) | ~m1_pre_topc(C_1029, A_1027) | v2_struct_0(C_1029) | ~m1_pre_topc(B_1028, A_1027) | v2_struct_0(B_1028) | ~l1_pre_topc(A_1027) | v2_struct_0(A_1027))), inference(resolution, [status(thm)], [c_13339, c_42])).
% 19.67/9.82  tff(c_14707, plain, (![A_1045, B_1046, C_1047]: (u1_struct_0(k2_tsep_1(A_1045, B_1046, C_1047))=k3_xboole_0(u1_struct_0(B_1046), u1_struct_0(C_1047)) | r1_tsep_1(B_1046, C_1047) | ~m1_pre_topc(C_1047, A_1045) | v2_struct_0(C_1047) | ~m1_pre_topc(B_1046, A_1045) | v2_struct_0(B_1046) | ~l1_pre_topc(A_1045) | v2_struct_0(A_1045))), inference(resolution, [status(thm)], [c_40, c_14160])).
% 19.67/9.82  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.67/9.82  tff(c_14887, plain, (![A_1045, B_1046, C_1047]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1045, B_1046, C_1047)), u1_struct_0(B_1046)) | r1_tsep_1(B_1046, C_1047) | ~m1_pre_topc(C_1047, A_1045) | v2_struct_0(C_1047) | ~m1_pre_topc(B_1046, A_1045) | v2_struct_0(B_1046) | ~l1_pre_topc(A_1045) | v2_struct_0(A_1045))), inference(superposition, [status(thm), theory('equality')], [c_14707, c_2])).
% 19.67/9.82  tff(c_21231, plain, (![A_1393]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1393, '#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(superposition, [status(thm), theory('equality')], [c_20954, c_14887])).
% 19.67/9.82  tff(c_21510, plain, (![A_1393]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1393, '#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_21231])).
% 19.67/9.82  tff(c_21511, plain, (![A_1393]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1393, '#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_52, c_21510])).
% 19.67/9.82  tff(c_97, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_94])).
% 19.67/9.82  tff(c_103, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97])).
% 19.67/9.82  tff(c_48, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 19.67/9.82  tff(c_116, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 19.67/9.82  tff(c_664, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_659, c_116])).
% 19.67/9.82  tff(c_668, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_664])).
% 19.67/9.82  tff(c_669, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_668])).
% 19.67/9.82  tff(c_21237, plain, (![A_1393]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_1393) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_1393) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393) | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(superposition, [status(thm), theory('equality')], [c_20954, c_14887])).
% 19.67/9.82  tff(c_21513, plain, (![A_1393]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393) | ~m1_pre_topc('#skF_3', A_1393) | ~m1_pre_topc('#skF_2', A_1393) | ~l1_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_21237])).
% 19.67/9.82  tff(c_23681, plain, (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_21513])).
% 19.67/9.82  tff(c_23683, plain, (![A_70]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_2', A_70) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(resolution, [status(thm)], [c_23681, c_46])).
% 19.67/9.82  tff(c_23705, plain, (![A_1445]: (~m1_pre_topc('#skF_2', A_1445) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_1445) | ~l1_pre_topc(A_1445) | ~v2_pre_topc(A_1445))), inference(negUnitSimplification, [status(thm)], [c_669, c_23683])).
% 19.67/9.82  tff(c_23713, plain, (~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_23705])).
% 19.67/9.82  tff(c_23723, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_23713])).
% 19.67/9.82  tff(c_23725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_23723])).
% 19.67/9.82  tff(c_23727, plain, (~r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_21513])).
% 19.67/9.82  tff(c_23730, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_21511, c_23727])).
% 19.67/9.82  tff(c_23742, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_23730])).
% 19.67/9.82  tff(c_23744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_23742])).
% 19.67/9.82  tff(c_23745, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 19.67/9.82  tff(c_24457, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24452, c_23745])).
% 19.67/9.82  tff(c_24461, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_24457])).
% 19.67/9.82  tff(c_24462, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_24461])).
% 19.67/9.82  tff(c_33967, plain, (![A_2181]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_2181) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', A_2181) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181) | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(superposition, [status(thm), theory('equality')], [c_33666, c_27867])).
% 19.67/9.82  tff(c_34213, plain, (![A_2181]: (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181) | ~m1_pre_topc('#skF_3', A_2181) | ~m1_pre_topc('#skF_2', A_2181) | ~l1_pre_topc(A_2181) | v2_struct_0(A_2181))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_52, c_33967])).
% 19.67/9.82  tff(c_35634, plain, (r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_34213])).
% 19.67/9.82  tff(c_35636, plain, (![A_70]: (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', A_70) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(resolution, [status(thm)], [c_35634, c_46])).
% 19.67/9.82  tff(c_35646, plain, (![A_2225]: (~m1_pre_topc('#skF_3', A_2225) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_2225) | ~l1_pre_topc(A_2225) | ~v2_pre_topc(A_2225))), inference(negUnitSimplification, [status(thm)], [c_24462, c_35636])).
% 19.67/9.82  tff(c_35654, plain, (~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_35646])).
% 19.67/9.82  tff(c_35661, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_64, c_35654])).
% 19.67/9.82  tff(c_35663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_56, c_35661])).
% 19.67/9.82  tff(c_35665, plain, (~r1_tarski(u1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_34213])).
% 19.67/9.82  tff(c_35668, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34211, c_35665])).
% 19.67/9.82  tff(c_35680, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_35668])).
% 19.67/9.82  tff(c_35682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_35680])).
% 19.67/9.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.67/9.82  
% 19.67/9.82  Inference rules
% 19.67/9.82  ----------------------
% 19.67/9.82  #Ref     : 4
% 19.67/9.82  #Sup     : 9867
% 19.67/9.82  #Fact    : 6
% 19.67/9.83  #Define  : 0
% 19.67/9.83  #Split   : 33
% 19.67/9.83  #Chain   : 0
% 19.67/9.83  #Close   : 0
% 19.67/9.83  
% 19.67/9.83  Ordering : KBO
% 19.67/9.83  
% 19.67/9.83  Simplification rules
% 19.67/9.83  ----------------------
% 19.67/9.83  #Subsume      : 634
% 19.67/9.83  #Demod        : 6890
% 19.67/9.83  #Tautology    : 1757
% 19.67/9.83  #SimpNegUnit  : 537
% 19.67/9.83  #BackRed      : 3
% 19.67/9.83  
% 19.67/9.83  #Partial instantiations: 0
% 19.67/9.83  #Strategies tried      : 1
% 19.67/9.83  
% 19.67/9.83  Timing (in seconds)
% 19.67/9.83  ----------------------
% 19.67/9.83  Preprocessing        : 0.38
% 19.67/9.83  Parsing              : 0.20
% 19.67/9.83  CNF conversion       : 0.03
% 19.67/9.83  Main loop            : 8.64
% 19.67/9.83  Inferencing          : 1.91
% 19.67/9.83  Reduction            : 2.98
% 19.67/9.83  Demodulation         : 2.44
% 19.67/9.83  BG Simplification    : 0.29
% 19.67/9.83  Subsumption          : 3.09
% 19.67/9.83  Abstraction          : 0.37
% 19.67/9.83  MUC search           : 0.00
% 19.67/9.83  Cooper               : 0.00
% 19.67/9.83  Total                : 9.09
% 19.67/9.83  Index Insertion      : 0.00
% 19.67/9.83  Index Deletion       : 0.00
% 19.67/9.83  Index Matching       : 0.00
% 19.67/9.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
